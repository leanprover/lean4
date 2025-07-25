// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Lean.MetavarContext Lean.Environment Lean.AddDecl Lean.Util.FoldConsts Lean.Meta.Basic Lean.Meta.Check Lean.Meta.Tactic.AuxLemma
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__4;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__6;
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__0;
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__6;
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_visitLevel___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_visitExpr___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__5;
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__9;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__0;
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__1;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_visitLevel___closed__1;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(uint8_t, uint8_t);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5;
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__8;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_visitExpr___closed__0;
extern lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_hash___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkBinding___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_visitLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_visitLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_194; 
x_194 = l_Lean_Level_hasMVar(x_2);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Level_hasParam(x_2);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_9);
return x_196;
}
else
{
goto block_193;
}
}
else
{
goto block_193;
}
block_30:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_24, 2, x_11);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
lean_ctor_set(x_24, 5, x_14);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_20);
x_25 = lean_st_ref_set(x_4, x_24, x_21);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_193:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_4, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_33);
x_38 = l_Lean_Meta_Closure_visitLevel___closed__0;
x_39 = lean_array_get_size(x_37);
x_40 = l_Lean_Level_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_37, x_51);
lean_dec_ref(x_37);
lean_inc(x_2);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_38, x_2, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_31);
x_54 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_55 = lean_apply_8(x_1, x_2, x_54, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_4, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_59, 5);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_59, 7);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_59, 8);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 9);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_59, 10);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_59, 11);
lean_inc_ref(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
x_76 = lean_array_get_size(x_75);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_49);
x_79 = lean_usize_land(x_47, x_78);
x_80 = lean_array_uget(x_75, x_79);
lean_inc(x_80);
lean_inc(x_2);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_38, x_2, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_74, x_82);
lean_dec(x_74);
lean_inc(x_56);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_56);
lean_ctor_set(x_84, 2, x_80);
x_85 = lean_array_uset(x_75, x_79, x_84);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_nat_mul(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Meta_Closure_visitLevel___closed__1;
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_92, x_85);
lean_ctor_set(x_60, 1, x_93);
lean_ctor_set(x_60, 0, x_83);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_60;
goto block_30;
}
else
{
lean_ctor_set(x_60, 1, x_85);
lean_ctor_set(x_60, 0, x_83);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_60;
goto block_30;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_75, x_79, x_94);
lean_inc(x_56);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_38, x_2, x_56, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
lean_ctor_set(x_60, 1, x_97);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_60;
goto block_30;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; size_t x_103; lean_object* x_104; uint8_t x_105; 
x_98 = lean_ctor_get(x_60, 0);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_60);
x_100 = lean_array_get_size(x_99);
x_101 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_102 = lean_usize_sub(x_101, x_49);
x_103 = lean_usize_land(x_47, x_102);
x_104 = lean_array_uget(x_99, x_103);
lean_inc(x_104);
lean_inc(x_2);
x_105 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_38, x_2, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
lean_inc(x_56);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_2);
lean_ctor_set(x_108, 1, x_56);
lean_ctor_set(x_108, 2, x_104);
x_109 = lean_array_uset(x_99, x_103, x_108);
x_110 = lean_unsigned_to_nat(4u);
x_111 = lean_nat_mul(x_107, x_110);
x_112 = lean_unsigned_to_nat(3u);
x_113 = lean_nat_div(x_111, x_112);
lean_dec(x_111);
x_114 = lean_array_get_size(x_109);
x_115 = lean_nat_dec_le(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = l_Lean_Meta_Closure_visitLevel___closed__1;
x_117 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_116, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_117);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_118;
goto block_30;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_109);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_119;
goto block_30;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_box(0);
x_121 = lean_array_uset(x_99, x_103, x_120);
lean_inc(x_56);
x_122 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_38, x_2, x_56, x_104);
x_123 = lean_array_uset(x_121, x_103, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_98);
lean_ctor_set(x_124, 1, x_123);
x_10 = x_62;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_61;
x_22 = x_56;
x_23 = x_124;
goto block_30;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_55;
}
}
else
{
lean_object* x_125; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_53, 0);
lean_inc(x_125);
lean_dec_ref(x_53);
lean_ctor_set(x_31, 0, x_125);
return x_31;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; size_t x_137; size_t x_138; size_t x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; 
x_126 = lean_ctor_get(x_31, 1);
lean_inc(x_126);
lean_dec(x_31);
x_127 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_33);
x_128 = l_Lean_Meta_Closure_visitLevel___closed__0;
x_129 = lean_array_get_size(x_127);
x_130 = l_Lean_Level_hash(x_2);
x_131 = 32;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = 16;
x_135 = lean_uint64_shift_right(x_133, x_134);
x_136 = lean_uint64_xor(x_133, x_135);
x_137 = lean_uint64_to_usize(x_136);
x_138 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_139 = 1;
x_140 = lean_usize_sub(x_138, x_139);
x_141 = lean_usize_land(x_137, x_140);
x_142 = lean_array_uget(x_127, x_141);
lean_dec_ref(x_127);
lean_inc(x_2);
x_143 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_128, x_2, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_145 = lean_apply_8(x_1, x_2, x_144, x_4, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; size_t x_169; lean_object* x_170; uint8_t x_171; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_st_ref_take(x_4, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec_ref(x_148);
x_152 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_149, 2);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_149, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_149, 4);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_149, 5);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_149, 6);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_149, 7);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_149, 8);
lean_inc(x_159);
x_160 = lean_ctor_get(x_149, 9);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_149, 10);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_149, 11);
lean_inc_ref(x_162);
lean_dec(x_149);
x_163 = lean_ctor_get(x_150, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_150, 1);
lean_inc_ref(x_164);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_165 = x_150;
} else {
 lean_dec_ref(x_150);
 x_165 = lean_box(0);
}
x_166 = lean_array_get_size(x_164);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = lean_usize_sub(x_167, x_139);
x_169 = lean_usize_land(x_137, x_168);
x_170 = lean_array_uget(x_164, x_169);
lean_inc(x_170);
lean_inc(x_2);
x_171 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_128, x_2, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_163, x_172);
lean_dec(x_163);
lean_inc(x_146);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_2);
lean_ctor_set(x_174, 1, x_146);
lean_ctor_set(x_174, 2, x_170);
x_175 = lean_array_uset(x_164, x_169, x_174);
x_176 = lean_unsigned_to_nat(4u);
x_177 = lean_nat_mul(x_173, x_176);
x_178 = lean_unsigned_to_nat(3u);
x_179 = lean_nat_div(x_177, x_178);
lean_dec(x_177);
x_180 = lean_array_get_size(x_175);
x_181 = lean_nat_dec_le(x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = l_Lean_Meta_Closure_visitLevel___closed__1;
x_183 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_182, x_175);
if (lean_is_scalar(x_165)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_165;
}
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_183);
x_10 = x_152;
x_11 = x_153;
x_12 = x_154;
x_13 = x_155;
x_14 = x_156;
x_15 = x_157;
x_16 = x_158;
x_17 = x_159;
x_18 = x_160;
x_19 = x_161;
x_20 = x_162;
x_21 = x_151;
x_22 = x_146;
x_23 = x_184;
goto block_30;
}
else
{
lean_object* x_185; 
if (lean_is_scalar(x_165)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_165;
}
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_175);
x_10 = x_152;
x_11 = x_153;
x_12 = x_154;
x_13 = x_155;
x_14 = x_156;
x_15 = x_157;
x_16 = x_158;
x_17 = x_159;
x_18 = x_160;
x_19 = x_161;
x_20 = x_162;
x_21 = x_151;
x_22 = x_146;
x_23 = x_185;
goto block_30;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_box(0);
x_187 = lean_array_uset(x_164, x_169, x_186);
lean_inc(x_146);
x_188 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_128, x_2, x_146, x_170);
x_189 = lean_array_uset(x_187, x_169, x_188);
if (lean_is_scalar(x_165)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_165;
}
lean_ctor_set(x_190, 0, x_163);
lean_ctor_set(x_190, 1, x_189);
x_10 = x_152;
x_11 = x_153;
x_12 = x_154;
x_13 = x_155;
x_14 = x_156;
x_15 = x_157;
x_16 = x_158;
x_17 = x_159;
x_18 = x_160;
x_19 = x_161;
x_20 = x_162;
x_21 = x_151;
x_22 = x_146;
x_23 = x_190;
goto block_30;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_145;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_143, 0);
lean_inc(x_191);
lean_dec_ref(x_143);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_126);
return x_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_Closure_visitLevel(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Closure_visitExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_visitExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_194; 
x_194 = l_Lean_Expr_hasLevelParam(x_2);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Expr_hasFVar(x_2);
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = l_Lean_Expr_hasMVar(x_2);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_9);
return x_197;
}
else
{
goto block_193;
}
}
else
{
goto block_193;
}
}
else
{
goto block_193;
}
block_30:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_14);
lean_ctor_set(x_24, 9, x_11);
lean_ctor_set(x_24, 10, x_16);
lean_ctor_set(x_24, 11, x_18);
x_25 = lean_st_ref_set(x_4, x_24, x_17);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_193:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_4, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_33);
x_38 = l_Lean_Meta_Closure_visitExpr___closed__0;
x_39 = lean_array_get_size(x_37);
x_40 = l_Lean_ExprStructEq_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_37, x_51);
lean_dec_ref(x_37);
lean_inc_ref(x_2);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_38, x_2, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_31);
x_54 = lean_box(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
x_55 = lean_apply_8(x_1, x_2, x_54, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_4, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_59, 5);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_59, 7);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_59, 8);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 9);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_59, 10);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_59, 11);
lean_inc_ref(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
x_76 = lean_array_get_size(x_75);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_49);
x_79 = lean_usize_land(x_47, x_78);
x_80 = lean_array_uget(x_75, x_79);
lean_inc(x_80);
lean_inc_ref(x_2);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_38, x_2, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_74, x_82);
lean_dec(x_74);
lean_inc(x_56);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_56);
lean_ctor_set(x_84, 2, x_80);
x_85 = lean_array_uset(x_75, x_79, x_84);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_nat_mul(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Meta_Closure_visitExpr___closed__1;
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_92, x_85);
lean_ctor_set(x_60, 1, x_93);
lean_ctor_set(x_60, 0, x_83);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_60;
goto block_30;
}
else
{
lean_ctor_set(x_60, 1, x_85);
lean_ctor_set(x_60, 0, x_83);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_60;
goto block_30;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_75, x_79, x_94);
lean_inc(x_56);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_38, x_2, x_56, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
lean_ctor_set(x_60, 1, x_97);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_60;
goto block_30;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; size_t x_103; lean_object* x_104; uint8_t x_105; 
x_98 = lean_ctor_get(x_60, 0);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_60);
x_100 = lean_array_get_size(x_99);
x_101 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_102 = lean_usize_sub(x_101, x_49);
x_103 = lean_usize_land(x_47, x_102);
x_104 = lean_array_uget(x_99, x_103);
lean_inc(x_104);
lean_inc_ref(x_2);
x_105 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_38, x_2, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
lean_inc(x_56);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_2);
lean_ctor_set(x_108, 1, x_56);
lean_ctor_set(x_108, 2, x_104);
x_109 = lean_array_uset(x_99, x_103, x_108);
x_110 = lean_unsigned_to_nat(4u);
x_111 = lean_nat_mul(x_107, x_110);
x_112 = lean_unsigned_to_nat(3u);
x_113 = lean_nat_div(x_111, x_112);
lean_dec(x_111);
x_114 = lean_array_get_size(x_109);
x_115 = lean_nat_dec_le(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = l_Lean_Meta_Closure_visitExpr___closed__1;
x_117 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_116, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_117);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_118;
goto block_30;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_109);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_119;
goto block_30;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_box(0);
x_121 = lean_array_uset(x_99, x_103, x_120);
lean_inc(x_56);
x_122 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_38, x_2, x_56, x_104);
x_123 = lean_array_uset(x_121, x_103, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_98);
lean_ctor_set(x_124, 1, x_123);
x_10 = x_56;
x_11 = x_70;
x_12 = x_64;
x_13 = x_66;
x_14 = x_69;
x_15 = x_63;
x_16 = x_71;
x_17 = x_61;
x_18 = x_72;
x_19 = x_62;
x_20 = x_65;
x_21 = x_67;
x_22 = x_68;
x_23 = x_124;
goto block_30;
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_2);
return x_55;
}
}
else
{
lean_object* x_125; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_53, 0);
lean_inc(x_125);
lean_dec_ref(x_53);
lean_ctor_set(x_31, 0, x_125);
return x_31;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; size_t x_137; size_t x_138; size_t x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; 
x_126 = lean_ctor_get(x_31, 1);
lean_inc(x_126);
lean_dec(x_31);
x_127 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_33);
x_128 = l_Lean_Meta_Closure_visitExpr___closed__0;
x_129 = lean_array_get_size(x_127);
x_130 = l_Lean_ExprStructEq_hash(x_2);
x_131 = 32;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = 16;
x_135 = lean_uint64_shift_right(x_133, x_134);
x_136 = lean_uint64_xor(x_133, x_135);
x_137 = lean_uint64_to_usize(x_136);
x_138 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_139 = 1;
x_140 = lean_usize_sub(x_138, x_139);
x_141 = lean_usize_land(x_137, x_140);
x_142 = lean_array_uget(x_127, x_141);
lean_dec_ref(x_127);
lean_inc_ref(x_2);
x_143 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_128, x_2, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_box(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
x_145 = lean_apply_8(x_1, x_2, x_144, x_4, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; size_t x_169; lean_object* x_170; uint8_t x_171; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_st_ref_take(x_4, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec_ref(x_148);
x_152 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_149, 2);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_149, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_149, 4);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_149, 5);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_149, 6);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_149, 7);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_149, 8);
lean_inc(x_159);
x_160 = lean_ctor_get(x_149, 9);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_149, 10);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_149, 11);
lean_inc_ref(x_162);
lean_dec(x_149);
x_163 = lean_ctor_get(x_150, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_150, 1);
lean_inc_ref(x_164);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_165 = x_150;
} else {
 lean_dec_ref(x_150);
 x_165 = lean_box(0);
}
x_166 = lean_array_get_size(x_164);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = lean_usize_sub(x_167, x_139);
x_169 = lean_usize_land(x_137, x_168);
x_170 = lean_array_uget(x_164, x_169);
lean_inc(x_170);
lean_inc_ref(x_2);
x_171 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_128, x_2, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_163, x_172);
lean_dec(x_163);
lean_inc(x_146);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_2);
lean_ctor_set(x_174, 1, x_146);
lean_ctor_set(x_174, 2, x_170);
x_175 = lean_array_uset(x_164, x_169, x_174);
x_176 = lean_unsigned_to_nat(4u);
x_177 = lean_nat_mul(x_173, x_176);
x_178 = lean_unsigned_to_nat(3u);
x_179 = lean_nat_div(x_177, x_178);
lean_dec(x_177);
x_180 = lean_array_get_size(x_175);
x_181 = lean_nat_dec_le(x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = l_Lean_Meta_Closure_visitExpr___closed__1;
x_183 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_182, x_175);
if (lean_is_scalar(x_165)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_165;
}
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_183);
x_10 = x_146;
x_11 = x_160;
x_12 = x_154;
x_13 = x_156;
x_14 = x_159;
x_15 = x_153;
x_16 = x_161;
x_17 = x_151;
x_18 = x_162;
x_19 = x_152;
x_20 = x_155;
x_21 = x_157;
x_22 = x_158;
x_23 = x_184;
goto block_30;
}
else
{
lean_object* x_185; 
if (lean_is_scalar(x_165)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_165;
}
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_175);
x_10 = x_146;
x_11 = x_160;
x_12 = x_154;
x_13 = x_156;
x_14 = x_159;
x_15 = x_153;
x_16 = x_161;
x_17 = x_151;
x_18 = x_162;
x_19 = x_152;
x_20 = x_155;
x_21 = x_157;
x_22 = x_158;
x_23 = x_185;
goto block_30;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_box(0);
x_187 = lean_array_uset(x_164, x_169, x_186);
lean_inc(x_146);
x_188 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_128, x_2, x_146, x_170);
x_189 = lean_array_uset(x_187, x_169, x_188);
if (lean_is_scalar(x_165)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_165;
}
lean_ctor_set(x_190, 0, x_163);
lean_ctor_set(x_190, 1, x_189);
x_10 = x_146;
x_11 = x_160;
x_12 = x_154;
x_13 = x_156;
x_14 = x_159;
x_15 = x_153;
x_16 = x_161;
x_17 = x_151;
x_18 = x_162;
x_19 = x_152;
x_20 = x_155;
x_21 = x_157;
x_22 = x_158;
x_23 = x_190;
goto block_30;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_2);
return x_145;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_143, 0);
lean_inc(x_191);
lean_dec_ref(x_143);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_126);
return x_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_Closure_visitExpr(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("u", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_st_ref_take(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_ctor_get(x_8, 3);
x_14 = lean_ctor_get(x_8, 4);
x_15 = l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1;
x_16 = lean_name_append_index_after(x_15, x_10);
lean_inc(x_16);
x_17 = lean_array_push(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_13, x_18);
lean_dec(x_13);
x_20 = lean_array_push(x_14, x_1);
lean_ctor_set(x_8, 4, x_20);
lean_ctor_set(x_8, 3, x_19);
lean_ctor_set(x_8, 2, x_17);
x_21 = lean_st_ref_set(x_2, x_8, x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_Lean_mkLevelParam(x_16);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_mkLevelParam(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 4);
x_33 = lean_ctor_get(x_8, 5);
x_34 = lean_ctor_get(x_8, 6);
x_35 = lean_ctor_get(x_8, 7);
x_36 = lean_ctor_get(x_8, 8);
x_37 = lean_ctor_get(x_8, 9);
x_38 = lean_ctor_get(x_8, 10);
x_39 = lean_ctor_get(x_8, 11);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_40 = l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1;
x_41 = lean_name_append_index_after(x_40, x_10);
lean_inc(x_41);
x_42 = lean_array_push(x_30, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_31, x_43);
lean_dec(x_31);
x_45 = lean_array_push(x_32, x_1);
x_46 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_29);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_33);
lean_ctor_set(x_46, 6, x_34);
lean_ctor_set(x_46, 7, x_35);
lean_ctor_set(x_46, 8, x_36);
lean_ctor_set(x_46, 9, x_37);
lean_ctor_set(x_46, 10, x_38);
lean_ctor_set(x_46, 11, x_39);
x_47 = lean_st_ref_set(x_2, x_46, x_9);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = l_Lean_mkLevelParam(x_41);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_level_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_level_eq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
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
x_26 = l_Lean_Level_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
x_8 = lean_level_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = lean_level_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_3);
return x_77;
}
case 1:
{
lean_object* x_78; uint8_t x_169; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_169 = l_Lean_Level_hasMVar(x_78);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Level_hasParam(x_78);
if (x_170 == 0)
{
x_29 = x_78;
x_30 = x_3;
goto block_33;
}
else
{
goto block_168;
}
}
else
{
goto block_168;
}
block_168:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; size_t x_92; size_t x_93; size_t x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_st_ref_get(x_2, x_3);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec_ref(x_79);
x_83 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_81);
x_84 = lean_array_get_size(x_83);
x_85 = l_Lean_Level_hash(x_78);
x_86 = 32;
x_87 = lean_uint64_shift_right(x_85, x_86);
x_88 = lean_uint64_xor(x_85, x_87);
x_89 = 16;
x_90 = lean_uint64_shift_right(x_88, x_89);
x_91 = lean_uint64_xor(x_88, x_90);
x_92 = lean_uint64_to_usize(x_91);
x_93 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_94 = 1;
x_95 = lean_usize_sub(x_93, x_94);
x_96 = lean_usize_land(x_92, x_95);
x_97 = lean_array_uget(x_83, x_96);
lean_dec_ref(x_83);
x_98 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_78, x_97);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_inc(x_78);
x_99 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_78, x_2, x_82);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_st_ref_take(x_2, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec_ref(x_102);
x_106 = lean_ctor_get(x_103, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_103, 2);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_103, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 4);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_103, 5);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_103, 6);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_103, 7);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_103, 8);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 9);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_103, 10);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_103, 11);
lean_inc_ref(x_116);
lean_dec(x_103);
x_117 = !lean_is_exclusive(x_104);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; size_t x_121; size_t x_122; size_t x_123; lean_object* x_124; uint8_t x_125; 
x_118 = lean_ctor_get(x_104, 0);
x_119 = lean_ctor_get(x_104, 1);
x_120 = lean_array_get_size(x_119);
x_121 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_122 = lean_usize_sub(x_121, x_94);
x_123 = lean_usize_land(x_92, x_122);
x_124 = lean_array_uget(x_119, x_123);
x_125 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_78, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_add(x_118, x_126);
lean_dec(x_118);
lean_inc(x_100);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_78);
lean_ctor_set(x_128, 1, x_100);
lean_ctor_set(x_128, 2, x_124);
x_129 = lean_array_uset(x_119, x_123, x_128);
x_130 = lean_unsigned_to_nat(4u);
x_131 = lean_nat_mul(x_127, x_130);
x_132 = lean_unsigned_to_nat(3u);
x_133 = lean_nat_div(x_131, x_132);
lean_dec(x_131);
x_134 = lean_array_get_size(x_129);
x_135 = lean_nat_dec_le(x_133, x_134);
lean_dec(x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_129);
lean_ctor_set(x_104, 1, x_136);
lean_ctor_set(x_104, 0, x_127);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_104;
goto block_51;
}
else
{
lean_ctor_set(x_104, 1, x_129);
lean_ctor_set(x_104, 0, x_127);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_104;
goto block_51;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_box(0);
x_138 = lean_array_uset(x_119, x_123, x_137);
lean_inc(x_100);
x_139 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_78, x_100, x_124);
x_140 = lean_array_uset(x_138, x_123, x_139);
lean_ctor_set(x_104, 1, x_140);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_104;
goto block_51;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; size_t x_144; size_t x_145; size_t x_146; lean_object* x_147; uint8_t x_148; 
x_141 = lean_ctor_get(x_104, 0);
x_142 = lean_ctor_get(x_104, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_104);
x_143 = lean_array_get_size(x_142);
x_144 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_145 = lean_usize_sub(x_144, x_94);
x_146 = lean_usize_land(x_92, x_145);
x_147 = lean_array_uget(x_142, x_146);
x_148 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_78, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_add(x_141, x_149);
lean_dec(x_141);
lean_inc(x_100);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_78);
lean_ctor_set(x_151, 1, x_100);
lean_ctor_set(x_151, 2, x_147);
x_152 = lean_array_uset(x_142, x_146, x_151);
x_153 = lean_unsigned_to_nat(4u);
x_154 = lean_nat_mul(x_150, x_153);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_div(x_154, x_155);
lean_dec(x_154);
x_157 = lean_array_get_size(x_152);
x_158 = lean_nat_dec_le(x_156, x_157);
lean_dec(x_157);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_152);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_159);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_160;
goto block_51;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_152);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_161;
goto block_51;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_box(0);
x_163 = lean_array_uset(x_142, x_146, x_162);
lean_inc(x_100);
x_164 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_78, x_100, x_147);
x_165 = lean_array_uset(x_163, x_146, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_141);
lean_ctor_set(x_166, 1, x_165);
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
x_37 = x_109;
x_38 = x_110;
x_39 = x_111;
x_40 = x_112;
x_41 = x_113;
x_42 = x_114;
x_43 = x_115;
x_44 = x_116;
x_45 = x_105;
x_46 = x_100;
x_47 = x_166;
goto block_51;
}
}
}
else
{
lean_object* x_167; 
lean_dec(x_78);
x_167 = lean_ctor_get(x_98, 0);
lean_inc(x_167);
lean_dec_ref(x_98);
x_29 = x_167;
x_30 = x_82;
goto block_33;
}
}
}
case 2:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_265; lean_object* x_266; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_378; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_1, 1);
lean_inc(x_172);
x_378 = l_Lean_Level_hasMVar(x_171);
if (x_378 == 0)
{
uint8_t x_379; 
x_379 = l_Lean_Level_hasParam(x_171);
if (x_379 == 0)
{
x_265 = x_171;
x_266 = x_3;
goto block_269;
}
else
{
goto block_377;
}
}
else
{
goto block_377;
}
block_264:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; 
x_175 = lean_st_ref_get(x_2, x_173);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_176, 0);
lean_inc_ref(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec_ref(x_175);
x_179 = lean_ctor_get(x_177, 1);
lean_inc_ref(x_179);
lean_dec_ref(x_177);
x_180 = lean_array_get_size(x_179);
x_181 = l_Lean_Level_hash(x_172);
x_182 = 32;
x_183 = lean_uint64_shift_right(x_181, x_182);
x_184 = lean_uint64_xor(x_181, x_183);
x_185 = 16;
x_186 = lean_uint64_shift_right(x_184, x_185);
x_187 = lean_uint64_xor(x_184, x_186);
x_188 = lean_uint64_to_usize(x_187);
x_189 = lean_usize_of_nat(x_180);
lean_dec(x_180);
x_190 = 1;
x_191 = lean_usize_sub(x_189, x_190);
x_192 = lean_usize_land(x_188, x_191);
x_193 = lean_array_uget(x_179, x_192);
lean_dec_ref(x_179);
x_194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_172, x_193);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_inc(x_172);
x_195 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_172, x_2, x_178);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_st_ref_take(x_2, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec_ref(x_198);
x_202 = lean_ctor_get(x_199, 1);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_199, 2);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_199, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 4);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_199, 5);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_199, 6);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_199, 7);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_199, 8);
lean_inc(x_209);
x_210 = lean_ctor_get(x_199, 9);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_199, 10);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_199, 11);
lean_inc_ref(x_212);
lean_dec(x_199);
x_213 = !lean_is_exclusive(x_200);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; size_t x_217; size_t x_218; size_t x_219; lean_object* x_220; uint8_t x_221; 
x_214 = lean_ctor_get(x_200, 0);
x_215 = lean_ctor_get(x_200, 1);
x_216 = lean_array_get_size(x_215);
x_217 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_218 = lean_usize_sub(x_217, x_190);
x_219 = lean_usize_land(x_188, x_218);
x_220 = lean_array_uget(x_215, x_219);
x_221 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_172, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_add(x_214, x_222);
lean_dec(x_214);
lean_inc(x_196);
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_172);
lean_ctor_set(x_224, 1, x_196);
lean_ctor_set(x_224, 2, x_220);
x_225 = lean_array_uset(x_215, x_219, x_224);
x_226 = lean_unsigned_to_nat(4u);
x_227 = lean_nat_mul(x_223, x_226);
x_228 = lean_unsigned_to_nat(3u);
x_229 = lean_nat_div(x_227, x_228);
lean_dec(x_227);
x_230 = lean_array_get_size(x_225);
x_231 = lean_nat_dec_le(x_229, x_230);
lean_dec(x_230);
lean_dec(x_229);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_225);
lean_ctor_set(x_200, 1, x_232);
lean_ctor_set(x_200, 0, x_223);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_200;
goto block_76;
}
else
{
lean_ctor_set(x_200, 1, x_225);
lean_ctor_set(x_200, 0, x_223);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_200;
goto block_76;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_box(0);
x_234 = lean_array_uset(x_215, x_219, x_233);
lean_inc(x_196);
x_235 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_172, x_196, x_220);
x_236 = lean_array_uset(x_234, x_219, x_235);
lean_ctor_set(x_200, 1, x_236);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_200;
goto block_76;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; size_t x_242; lean_object* x_243; uint8_t x_244; 
x_237 = lean_ctor_get(x_200, 0);
x_238 = lean_ctor_get(x_200, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_200);
x_239 = lean_array_get_size(x_238);
x_240 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_241 = lean_usize_sub(x_240, x_190);
x_242 = lean_usize_land(x_188, x_241);
x_243 = lean_array_uget(x_238, x_242);
x_244 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_172, x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_nat_add(x_237, x_245);
lean_dec(x_237);
lean_inc(x_196);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_172);
lean_ctor_set(x_247, 1, x_196);
lean_ctor_set(x_247, 2, x_243);
x_248 = lean_array_uset(x_238, x_242, x_247);
x_249 = lean_unsigned_to_nat(4u);
x_250 = lean_nat_mul(x_246, x_249);
x_251 = lean_unsigned_to_nat(3u);
x_252 = lean_nat_div(x_250, x_251);
lean_dec(x_250);
x_253 = lean_array_get_size(x_248);
x_254 = lean_nat_dec_le(x_252, x_253);
lean_dec(x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_248);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_246);
lean_ctor_set(x_256, 1, x_255);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_256;
goto block_76;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_246);
lean_ctor_set(x_257, 1, x_248);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_257;
goto block_76;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_box(0);
x_259 = lean_array_uset(x_238, x_242, x_258);
lean_inc(x_196);
x_260 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_172, x_196, x_243);
x_261 = lean_array_uset(x_259, x_242, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_237);
lean_ctor_set(x_262, 1, x_261);
x_58 = x_201;
x_59 = x_196;
x_60 = x_202;
x_61 = x_203;
x_62 = x_204;
x_63 = x_205;
x_64 = x_206;
x_65 = x_207;
x_66 = x_208;
x_67 = x_209;
x_68 = x_210;
x_69 = x_211;
x_70 = x_212;
x_71 = x_174;
x_72 = x_262;
goto block_76;
}
}
}
else
{
lean_object* x_263; 
lean_dec(x_172);
x_263 = lean_ctor_get(x_194, 0);
lean_inc(x_263);
lean_dec_ref(x_194);
x_52 = x_174;
x_53 = x_263;
x_54 = x_178;
goto block_57;
}
}
block_269:
{
uint8_t x_267; 
x_267 = l_Lean_Level_hasMVar(x_172);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = l_Lean_Level_hasParam(x_172);
if (x_268 == 0)
{
x_52 = x_265;
x_53 = x_172;
x_54 = x_266;
goto block_57;
}
else
{
x_173 = x_266;
x_174 = x_265;
goto block_264;
}
}
else
{
x_173 = x_266;
x_174 = x_265;
goto block_264;
}
}
block_287:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_271);
lean_ctor_set(x_284, 2, x_272);
lean_ctor_set(x_284, 3, x_273);
lean_ctor_set(x_284, 4, x_274);
lean_ctor_set(x_284, 5, x_275);
lean_ctor_set(x_284, 6, x_276);
lean_ctor_set(x_284, 7, x_277);
lean_ctor_set(x_284, 8, x_278);
lean_ctor_set(x_284, 9, x_279);
lean_ctor_set(x_284, 10, x_280);
lean_ctor_set(x_284, 11, x_281);
x_285 = lean_st_ref_set(x_2, x_284, x_282);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec_ref(x_285);
x_265 = x_270;
x_266 = x_286;
goto block_269;
}
block_377:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint64_t x_294; uint64_t x_295; uint64_t x_296; uint64_t x_297; uint64_t x_298; uint64_t x_299; uint64_t x_300; size_t x_301; size_t x_302; size_t x_303; size_t x_304; size_t x_305; lean_object* x_306; lean_object* x_307; 
x_288 = lean_st_ref_get(x_2, x_3);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_289, 0);
lean_inc_ref(x_290);
lean_dec(x_289);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec_ref(x_288);
x_292 = lean_ctor_get(x_290, 1);
lean_inc_ref(x_292);
lean_dec_ref(x_290);
x_293 = lean_array_get_size(x_292);
x_294 = l_Lean_Level_hash(x_171);
x_295 = 32;
x_296 = lean_uint64_shift_right(x_294, x_295);
x_297 = lean_uint64_xor(x_294, x_296);
x_298 = 16;
x_299 = lean_uint64_shift_right(x_297, x_298);
x_300 = lean_uint64_xor(x_297, x_299);
x_301 = lean_uint64_to_usize(x_300);
x_302 = lean_usize_of_nat(x_293);
lean_dec(x_293);
x_303 = 1;
x_304 = lean_usize_sub(x_302, x_303);
x_305 = lean_usize_land(x_301, x_304);
x_306 = lean_array_uget(x_292, x_305);
lean_dec_ref(x_292);
x_307 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_171, x_306);
lean_dec(x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
lean_inc(x_171);
x_308 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_171, x_2, x_291);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec_ref(x_308);
x_311 = lean_st_ref_take(x_2, x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 0);
lean_inc_ref(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec_ref(x_311);
x_315 = lean_ctor_get(x_312, 1);
lean_inc_ref(x_315);
x_316 = lean_ctor_get(x_312, 2);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_312, 3);
lean_inc(x_317);
x_318 = lean_ctor_get(x_312, 4);
lean_inc_ref(x_318);
x_319 = lean_ctor_get(x_312, 5);
lean_inc_ref(x_319);
x_320 = lean_ctor_get(x_312, 6);
lean_inc_ref(x_320);
x_321 = lean_ctor_get(x_312, 7);
lean_inc_ref(x_321);
x_322 = lean_ctor_get(x_312, 8);
lean_inc(x_322);
x_323 = lean_ctor_get(x_312, 9);
lean_inc_ref(x_323);
x_324 = lean_ctor_get(x_312, 10);
lean_inc_ref(x_324);
x_325 = lean_ctor_get(x_312, 11);
lean_inc_ref(x_325);
lean_dec(x_312);
x_326 = !lean_is_exclusive(x_313);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; size_t x_330; size_t x_331; size_t x_332; lean_object* x_333; uint8_t x_334; 
x_327 = lean_ctor_get(x_313, 0);
x_328 = lean_ctor_get(x_313, 1);
x_329 = lean_array_get_size(x_328);
x_330 = lean_usize_of_nat(x_329);
lean_dec(x_329);
x_331 = lean_usize_sub(x_330, x_303);
x_332 = lean_usize_land(x_301, x_331);
x_333 = lean_array_uget(x_328, x_332);
x_334 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_171, x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_335 = lean_unsigned_to_nat(1u);
x_336 = lean_nat_add(x_327, x_335);
lean_dec(x_327);
lean_inc(x_309);
x_337 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_337, 0, x_171);
lean_ctor_set(x_337, 1, x_309);
lean_ctor_set(x_337, 2, x_333);
x_338 = lean_array_uset(x_328, x_332, x_337);
x_339 = lean_unsigned_to_nat(4u);
x_340 = lean_nat_mul(x_336, x_339);
x_341 = lean_unsigned_to_nat(3u);
x_342 = lean_nat_div(x_340, x_341);
lean_dec(x_340);
x_343 = lean_array_get_size(x_338);
x_344 = lean_nat_dec_le(x_342, x_343);
lean_dec(x_343);
lean_dec(x_342);
if (x_344 == 0)
{
lean_object* x_345; 
x_345 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_338);
lean_ctor_set(x_313, 1, x_345);
lean_ctor_set(x_313, 0, x_336);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_313;
goto block_287;
}
else
{
lean_ctor_set(x_313, 1, x_338);
lean_ctor_set(x_313, 0, x_336);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_313;
goto block_287;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_box(0);
x_347 = lean_array_uset(x_328, x_332, x_346);
lean_inc(x_309);
x_348 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_171, x_309, x_333);
x_349 = lean_array_uset(x_347, x_332, x_348);
lean_ctor_set(x_313, 1, x_349);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_313;
goto block_287;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; size_t x_353; size_t x_354; size_t x_355; lean_object* x_356; uint8_t x_357; 
x_350 = lean_ctor_get(x_313, 0);
x_351 = lean_ctor_get(x_313, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_313);
x_352 = lean_array_get_size(x_351);
x_353 = lean_usize_of_nat(x_352);
lean_dec(x_352);
x_354 = lean_usize_sub(x_353, x_303);
x_355 = lean_usize_land(x_301, x_354);
x_356 = lean_array_uget(x_351, x_355);
x_357 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_171, x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_358 = lean_unsigned_to_nat(1u);
x_359 = lean_nat_add(x_350, x_358);
lean_dec(x_350);
lean_inc(x_309);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_171);
lean_ctor_set(x_360, 1, x_309);
lean_ctor_set(x_360, 2, x_356);
x_361 = lean_array_uset(x_351, x_355, x_360);
x_362 = lean_unsigned_to_nat(4u);
x_363 = lean_nat_mul(x_359, x_362);
x_364 = lean_unsigned_to_nat(3u);
x_365 = lean_nat_div(x_363, x_364);
lean_dec(x_363);
x_366 = lean_array_get_size(x_361);
x_367 = lean_nat_dec_le(x_365, x_366);
lean_dec(x_366);
lean_dec(x_365);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_361);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_359);
lean_ctor_set(x_369, 1, x_368);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_369;
goto block_287;
}
else
{
lean_object* x_370; 
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_359);
lean_ctor_set(x_370, 1, x_361);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_370;
goto block_287;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_box(0);
x_372 = lean_array_uset(x_351, x_355, x_371);
lean_inc(x_309);
x_373 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_171, x_309, x_356);
x_374 = lean_array_uset(x_372, x_355, x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_350);
lean_ctor_set(x_375, 1, x_374);
x_270 = x_309;
x_271 = x_315;
x_272 = x_316;
x_273 = x_317;
x_274 = x_318;
x_275 = x_319;
x_276 = x_320;
x_277 = x_321;
x_278 = x_322;
x_279 = x_323;
x_280 = x_324;
x_281 = x_325;
x_282 = x_314;
x_283 = x_375;
goto block_287;
}
}
}
else
{
lean_object* x_376; 
lean_dec(x_171);
x_376 = lean_ctor_get(x_307, 0);
lean_inc(x_376);
lean_dec_ref(x_307);
x_265 = x_376;
x_266 = x_291;
goto block_269;
}
}
}
case 3:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_474; lean_object* x_475; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_587; 
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
x_587 = l_Lean_Level_hasMVar(x_380);
if (x_587 == 0)
{
uint8_t x_588; 
x_588 = l_Lean_Level_hasParam(x_380);
if (x_588 == 0)
{
x_474 = x_380;
x_475 = x_3;
goto block_478;
}
else
{
goto block_586;
}
}
else
{
goto block_586;
}
block_473:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint64_t x_390; uint64_t x_391; uint64_t x_392; uint64_t x_393; uint64_t x_394; uint64_t x_395; uint64_t x_396; size_t x_397; size_t x_398; size_t x_399; size_t x_400; size_t x_401; lean_object* x_402; lean_object* x_403; 
x_384 = lean_st_ref_get(x_2, x_383);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 0);
lean_inc_ref(x_386);
lean_dec(x_385);
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
lean_dec_ref(x_384);
x_388 = lean_ctor_get(x_386, 1);
lean_inc_ref(x_388);
lean_dec_ref(x_386);
x_389 = lean_array_get_size(x_388);
x_390 = l_Lean_Level_hash(x_381);
x_391 = 32;
x_392 = lean_uint64_shift_right(x_390, x_391);
x_393 = lean_uint64_xor(x_390, x_392);
x_394 = 16;
x_395 = lean_uint64_shift_right(x_393, x_394);
x_396 = lean_uint64_xor(x_393, x_395);
x_397 = lean_uint64_to_usize(x_396);
x_398 = lean_usize_of_nat(x_389);
lean_dec(x_389);
x_399 = 1;
x_400 = lean_usize_sub(x_398, x_399);
x_401 = lean_usize_land(x_397, x_400);
x_402 = lean_array_uget(x_388, x_401);
lean_dec_ref(x_388);
x_403 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_381, x_402);
lean_dec(x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
lean_inc(x_381);
x_404 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_381, x_2, x_387);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec_ref(x_404);
x_407 = lean_st_ref_take(x_2, x_406);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_408, 0);
lean_inc_ref(x_409);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec_ref(x_407);
x_411 = lean_ctor_get(x_408, 1);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_408, 2);
lean_inc_ref(x_412);
x_413 = lean_ctor_get(x_408, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_408, 4);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_408, 5);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_408, 6);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_408, 7);
lean_inc_ref(x_417);
x_418 = lean_ctor_get(x_408, 8);
lean_inc(x_418);
x_419 = lean_ctor_get(x_408, 9);
lean_inc_ref(x_419);
x_420 = lean_ctor_get(x_408, 10);
lean_inc_ref(x_420);
x_421 = lean_ctor_get(x_408, 11);
lean_inc_ref(x_421);
lean_dec(x_408);
x_422 = !lean_is_exclusive(x_409);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; size_t x_426; size_t x_427; size_t x_428; lean_object* x_429; uint8_t x_430; 
x_423 = lean_ctor_get(x_409, 0);
x_424 = lean_ctor_get(x_409, 1);
x_425 = lean_array_get_size(x_424);
x_426 = lean_usize_of_nat(x_425);
lean_dec(x_425);
x_427 = lean_usize_sub(x_426, x_399);
x_428 = lean_usize_land(x_397, x_427);
x_429 = lean_array_uget(x_424, x_428);
x_430 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_381, x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_nat_add(x_423, x_431);
lean_dec(x_423);
lean_inc(x_405);
x_433 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_433, 0, x_381);
lean_ctor_set(x_433, 1, x_405);
lean_ctor_set(x_433, 2, x_429);
x_434 = lean_array_uset(x_424, x_428, x_433);
x_435 = lean_unsigned_to_nat(4u);
x_436 = lean_nat_mul(x_432, x_435);
x_437 = lean_unsigned_to_nat(3u);
x_438 = lean_nat_div(x_436, x_437);
lean_dec(x_436);
x_439 = lean_array_get_size(x_434);
x_440 = lean_nat_dec_le(x_438, x_439);
lean_dec(x_439);
lean_dec(x_438);
if (x_440 == 0)
{
lean_object* x_441; 
x_441 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_434);
lean_ctor_set(x_409, 1, x_441);
lean_ctor_set(x_409, 0, x_432);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_409;
goto block_28;
}
else
{
lean_ctor_set(x_409, 1, x_434);
lean_ctor_set(x_409, 0, x_432);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_409;
goto block_28;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_box(0);
x_443 = lean_array_uset(x_424, x_428, x_442);
lean_inc(x_405);
x_444 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_381, x_405, x_429);
x_445 = lean_array_uset(x_443, x_428, x_444);
lean_ctor_set(x_409, 1, x_445);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_409;
goto block_28;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; size_t x_449; size_t x_450; size_t x_451; lean_object* x_452; uint8_t x_453; 
x_446 = lean_ctor_get(x_409, 0);
x_447 = lean_ctor_get(x_409, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_409);
x_448 = lean_array_get_size(x_447);
x_449 = lean_usize_of_nat(x_448);
lean_dec(x_448);
x_450 = lean_usize_sub(x_449, x_399);
x_451 = lean_usize_land(x_397, x_450);
x_452 = lean_array_uget(x_447, x_451);
x_453 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_381, x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
x_454 = lean_unsigned_to_nat(1u);
x_455 = lean_nat_add(x_446, x_454);
lean_dec(x_446);
lean_inc(x_405);
x_456 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_456, 0, x_381);
lean_ctor_set(x_456, 1, x_405);
lean_ctor_set(x_456, 2, x_452);
x_457 = lean_array_uset(x_447, x_451, x_456);
x_458 = lean_unsigned_to_nat(4u);
x_459 = lean_nat_mul(x_455, x_458);
x_460 = lean_unsigned_to_nat(3u);
x_461 = lean_nat_div(x_459, x_460);
lean_dec(x_459);
x_462 = lean_array_get_size(x_457);
x_463 = lean_nat_dec_le(x_461, x_462);
lean_dec(x_462);
lean_dec(x_461);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; 
x_464 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_457);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_455);
lean_ctor_set(x_465, 1, x_464);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_465;
goto block_28;
}
else
{
lean_object* x_466; 
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_455);
lean_ctor_set(x_466, 1, x_457);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_466;
goto block_28;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_467 = lean_box(0);
x_468 = lean_array_uset(x_447, x_451, x_467);
lean_inc(x_405);
x_469 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_381, x_405, x_452);
x_470 = lean_array_uset(x_468, x_451, x_469);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_446);
lean_ctor_set(x_471, 1, x_470);
x_10 = x_382;
x_11 = x_410;
x_12 = x_411;
x_13 = x_412;
x_14 = x_413;
x_15 = x_414;
x_16 = x_415;
x_17 = x_416;
x_18 = x_417;
x_19 = x_418;
x_20 = x_419;
x_21 = x_420;
x_22 = x_421;
x_23 = x_405;
x_24 = x_471;
goto block_28;
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_381);
x_472 = lean_ctor_get(x_403, 0);
lean_inc(x_472);
lean_dec_ref(x_403);
x_4 = x_382;
x_5 = x_472;
x_6 = x_387;
goto block_9;
}
}
block_478:
{
uint8_t x_476; 
x_476 = l_Lean_Level_hasMVar(x_381);
if (x_476 == 0)
{
uint8_t x_477; 
x_477 = l_Lean_Level_hasParam(x_381);
if (x_477 == 0)
{
x_4 = x_474;
x_5 = x_381;
x_6 = x_475;
goto block_9;
}
else
{
x_382 = x_474;
x_383 = x_475;
goto block_473;
}
}
else
{
x_382 = x_474;
x_383 = x_475;
goto block_473;
}
}
block_496:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_480);
lean_ctor_set(x_493, 2, x_481);
lean_ctor_set(x_493, 3, x_482);
lean_ctor_set(x_493, 4, x_483);
lean_ctor_set(x_493, 5, x_484);
lean_ctor_set(x_493, 6, x_485);
lean_ctor_set(x_493, 7, x_486);
lean_ctor_set(x_493, 8, x_487);
lean_ctor_set(x_493, 9, x_488);
lean_ctor_set(x_493, 10, x_489);
lean_ctor_set(x_493, 11, x_490);
x_494 = lean_st_ref_set(x_2, x_493, x_479);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec_ref(x_494);
x_474 = x_491;
x_475 = x_495;
goto block_478;
}
block_586:
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint64_t x_503; uint64_t x_504; uint64_t x_505; uint64_t x_506; uint64_t x_507; uint64_t x_508; uint64_t x_509; size_t x_510; size_t x_511; size_t x_512; size_t x_513; size_t x_514; lean_object* x_515; lean_object* x_516; 
x_497 = lean_st_ref_get(x_2, x_3);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_498, 0);
lean_inc_ref(x_499);
lean_dec(x_498);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec_ref(x_497);
x_501 = lean_ctor_get(x_499, 1);
lean_inc_ref(x_501);
lean_dec_ref(x_499);
x_502 = lean_array_get_size(x_501);
x_503 = l_Lean_Level_hash(x_380);
x_504 = 32;
x_505 = lean_uint64_shift_right(x_503, x_504);
x_506 = lean_uint64_xor(x_503, x_505);
x_507 = 16;
x_508 = lean_uint64_shift_right(x_506, x_507);
x_509 = lean_uint64_xor(x_506, x_508);
x_510 = lean_uint64_to_usize(x_509);
x_511 = lean_usize_of_nat(x_502);
lean_dec(x_502);
x_512 = 1;
x_513 = lean_usize_sub(x_511, x_512);
x_514 = lean_usize_land(x_510, x_513);
x_515 = lean_array_uget(x_501, x_514);
lean_dec_ref(x_501);
x_516 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_380, x_515);
lean_dec(x_515);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
lean_inc(x_380);
x_517 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_380, x_2, x_500);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec_ref(x_517);
x_520 = lean_st_ref_take(x_2, x_519);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_521, 0);
lean_inc_ref(x_522);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
lean_dec_ref(x_520);
x_524 = lean_ctor_get(x_521, 1);
lean_inc_ref(x_524);
x_525 = lean_ctor_get(x_521, 2);
lean_inc_ref(x_525);
x_526 = lean_ctor_get(x_521, 3);
lean_inc(x_526);
x_527 = lean_ctor_get(x_521, 4);
lean_inc_ref(x_527);
x_528 = lean_ctor_get(x_521, 5);
lean_inc_ref(x_528);
x_529 = lean_ctor_get(x_521, 6);
lean_inc_ref(x_529);
x_530 = lean_ctor_get(x_521, 7);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_521, 8);
lean_inc(x_531);
x_532 = lean_ctor_get(x_521, 9);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_521, 10);
lean_inc_ref(x_533);
x_534 = lean_ctor_get(x_521, 11);
lean_inc_ref(x_534);
lean_dec(x_521);
x_535 = !lean_is_exclusive(x_522);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; size_t x_539; size_t x_540; size_t x_541; lean_object* x_542; uint8_t x_543; 
x_536 = lean_ctor_get(x_522, 0);
x_537 = lean_ctor_get(x_522, 1);
x_538 = lean_array_get_size(x_537);
x_539 = lean_usize_of_nat(x_538);
lean_dec(x_538);
x_540 = lean_usize_sub(x_539, x_512);
x_541 = lean_usize_land(x_510, x_540);
x_542 = lean_array_uget(x_537, x_541);
x_543 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_380, x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_544 = lean_unsigned_to_nat(1u);
x_545 = lean_nat_add(x_536, x_544);
lean_dec(x_536);
lean_inc(x_518);
x_546 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_546, 0, x_380);
lean_ctor_set(x_546, 1, x_518);
lean_ctor_set(x_546, 2, x_542);
x_547 = lean_array_uset(x_537, x_541, x_546);
x_548 = lean_unsigned_to_nat(4u);
x_549 = lean_nat_mul(x_545, x_548);
x_550 = lean_unsigned_to_nat(3u);
x_551 = lean_nat_div(x_549, x_550);
lean_dec(x_549);
x_552 = lean_array_get_size(x_547);
x_553 = lean_nat_dec_le(x_551, x_552);
lean_dec(x_552);
lean_dec(x_551);
if (x_553 == 0)
{
lean_object* x_554; 
x_554 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_547);
lean_ctor_set(x_522, 1, x_554);
lean_ctor_set(x_522, 0, x_545);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_522;
goto block_496;
}
else
{
lean_ctor_set(x_522, 1, x_547);
lean_ctor_set(x_522, 0, x_545);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_522;
goto block_496;
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_555 = lean_box(0);
x_556 = lean_array_uset(x_537, x_541, x_555);
lean_inc(x_518);
x_557 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_380, x_518, x_542);
x_558 = lean_array_uset(x_556, x_541, x_557);
lean_ctor_set(x_522, 1, x_558);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_522;
goto block_496;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; size_t x_562; size_t x_563; size_t x_564; lean_object* x_565; uint8_t x_566; 
x_559 = lean_ctor_get(x_522, 0);
x_560 = lean_ctor_get(x_522, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_522);
x_561 = lean_array_get_size(x_560);
x_562 = lean_usize_of_nat(x_561);
lean_dec(x_561);
x_563 = lean_usize_sub(x_562, x_512);
x_564 = lean_usize_land(x_510, x_563);
x_565 = lean_array_uget(x_560, x_564);
x_566 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_380, x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_567 = lean_unsigned_to_nat(1u);
x_568 = lean_nat_add(x_559, x_567);
lean_dec(x_559);
lean_inc(x_518);
x_569 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_569, 0, x_380);
lean_ctor_set(x_569, 1, x_518);
lean_ctor_set(x_569, 2, x_565);
x_570 = lean_array_uset(x_560, x_564, x_569);
x_571 = lean_unsigned_to_nat(4u);
x_572 = lean_nat_mul(x_568, x_571);
x_573 = lean_unsigned_to_nat(3u);
x_574 = lean_nat_div(x_572, x_573);
lean_dec(x_572);
x_575 = lean_array_get_size(x_570);
x_576 = lean_nat_dec_le(x_574, x_575);
lean_dec(x_575);
lean_dec(x_574);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
x_577 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_570);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_568);
lean_ctor_set(x_578, 1, x_577);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_578;
goto block_496;
}
else
{
lean_object* x_579; 
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_568);
lean_ctor_set(x_579, 1, x_570);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_579;
goto block_496;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_580 = lean_box(0);
x_581 = lean_array_uset(x_560, x_564, x_580);
lean_inc(x_518);
x_582 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_380, x_518, x_565);
x_583 = lean_array_uset(x_581, x_564, x_582);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_559);
lean_ctor_set(x_584, 1, x_583);
x_479 = x_523;
x_480 = x_524;
x_481 = x_525;
x_482 = x_526;
x_483 = x_527;
x_484 = x_528;
x_485 = x_529;
x_486 = x_530;
x_487 = x_531;
x_488 = x_532;
x_489 = x_533;
x_490 = x_534;
x_491 = x_518;
x_492 = x_584;
goto block_496;
}
}
}
else
{
lean_object* x_585; 
lean_dec(x_380);
x_585 = lean_ctor_get(x_516, 0);
lean_inc(x_585);
lean_dec_ref(x_516);
x_474 = x_585;
x_475 = x_500;
goto block_478;
}
}
}
default: 
{
lean_object* x_589; 
x_589 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_2, x_3);
return x_589;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(x_1, x_4, x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_14);
lean_ctor_set(x_25, 4, x_15);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_19);
lean_ctor_set(x_25, 9, x_20);
lean_ctor_set(x_25, 10, x_21);
lean_ctor_set(x_25, 11, x_22);
x_26 = lean_st_ref_set(x_2, x_25, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_4 = x_10;
x_5 = x_23;
x_6 = x_27;
goto block_9;
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(x_1, x_29);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
lean_ctor_set(x_48, 4, x_37);
lean_ctor_set(x_48, 5, x_38);
lean_ctor_set(x_48, 6, x_39);
lean_ctor_set(x_48, 7, x_40);
lean_ctor_set(x_48, 8, x_41);
lean_ctor_set(x_48, 9, x_42);
lean_ctor_set(x_48, 10, x_43);
lean_ctor_set(x_48, 11, x_44);
x_49 = lean_st_ref_set(x_2, x_48, x_45);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_29 = x_46;
x_30 = x_50;
goto block_33;
}
block_57:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(x_1, x_52, x_53);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
block_76:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_63);
lean_ctor_set(x_73, 5, x_64);
lean_ctor_set(x_73, 6, x_65);
lean_ctor_set(x_73, 7, x_66);
lean_ctor_set(x_73, 8, x_67);
lean_ctor_set(x_73, 9, x_68);
lean_ctor_set(x_73, 10, x_69);
lean_ctor_set(x_73, 11, x_70);
x_74 = lean_st_ref_set(x_2, x_73, x_58);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
x_52 = x_71;
x_53 = x_59;
x_54 = x_75;
goto block_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_181; 
x_181 = l_Lean_Level_hasMVar(x_1);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_Level_hasParam(x_1);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_3);
return x_183;
}
else
{
goto block_180;
}
}
else
{
goto block_180;
}
block_24:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
lean_ctor_set(x_18, 3, x_8);
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 5, x_10);
lean_ctor_set(x_18, 6, x_11);
lean_ctor_set(x_18, 7, x_12);
lean_ctor_set(x_18, 8, x_13);
lean_ctor_set(x_18, 9, x_14);
lean_ctor_set(x_18, 10, x_15);
lean_ctor_set(x_18, 11, x_16);
x_19 = lean_st_ref_set(x_2, x_18, x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
block_180:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_st_ref_get(x_2, x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_27);
x_32 = lean_array_get_size(x_31);
x_33 = l_Lean_Level_hash(x_1);
x_34 = 32;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = 16;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_42 = 1;
x_43 = lean_usize_sub(x_41, x_42);
x_44 = lean_usize_land(x_40, x_43);
x_45 = lean_array_uget(x_31, x_44);
lean_dec_ref(x_31);
x_46 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_25);
lean_inc(x_1);
x_47 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_29);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_st_ref_take(x_2, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec_ref(x_50);
x_54 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 4);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_51, 5);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_51, 6);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_51, 7);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_51, 8);
lean_inc(x_61);
x_62 = lean_ctor_get(x_51, 9);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_51, 10);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_51, 11);
lean_inc_ref(x_64);
lean_dec(x_51);
x_65 = !lean_is_exclusive(x_52);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; size_t x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
x_68 = lean_array_get_size(x_67);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = lean_usize_sub(x_69, x_42);
x_71 = lean_usize_land(x_40, x_70);
x_72 = lean_array_uget(x_67, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_66, x_74);
lean_dec(x_66);
lean_inc(x_48);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_48);
lean_ctor_set(x_76, 2, x_72);
x_77 = lean_array_uset(x_67, x_71, x_76);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_mul(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_77);
lean_ctor_set(x_52, 1, x_84);
lean_ctor_set(x_52, 0, x_75);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_52;
goto block_24;
}
else
{
lean_ctor_set(x_52, 1, x_77);
lean_ctor_set(x_52, 0, x_75);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_52;
goto block_24;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_array_uset(x_67, x_71, x_85);
lean_inc(x_48);
x_87 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_48, x_72);
x_88 = lean_array_uset(x_86, x_71, x_87);
lean_ctor_set(x_52, 1, x_88);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_52;
goto block_24;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; size_t x_92; size_t x_93; size_t x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_52, 0);
x_90 = lean_ctor_get(x_52, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_52);
x_91 = lean_array_get_size(x_90);
x_92 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_93 = lean_usize_sub(x_92, x_42);
x_94 = lean_usize_land(x_40, x_93);
x_95 = lean_array_uget(x_90, x_94);
x_96 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_89, x_97);
lean_dec(x_89);
lean_inc(x_48);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_48);
lean_ctor_set(x_99, 2, x_95);
x_100 = lean_array_uset(x_90, x_94, x_99);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_mul(x_98, x_101);
x_103 = lean_unsigned_to_nat(3u);
x_104 = lean_nat_div(x_102, x_103);
lean_dec(x_102);
x_105 = lean_array_get_size(x_100);
x_106 = lean_nat_dec_le(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_108;
goto block_24;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_100);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_109;
goto block_24;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_box(0);
x_111 = lean_array_uset(x_90, x_94, x_110);
lean_inc(x_48);
x_112 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_48, x_95);
x_113 = lean_array_uset(x_111, x_94, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_89);
lean_ctor_set(x_114, 1, x_113);
x_4 = x_48;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
x_8 = x_56;
x_9 = x_57;
x_10 = x_58;
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
x_15 = x_63;
x_16 = x_64;
x_17 = x_114;
goto block_24;
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_1);
x_115 = lean_ctor_get(x_46, 0);
lean_inc(x_115);
lean_dec_ref(x_46);
lean_ctor_set(x_25, 0, x_115);
return x_25;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; size_t x_126; size_t x_127; size_t x_128; size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_25, 1);
lean_inc(x_116);
lean_dec(x_25);
x_117 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_117);
lean_dec_ref(x_27);
x_118 = lean_array_get_size(x_117);
x_119 = l_Lean_Level_hash(x_1);
x_120 = 32;
x_121 = lean_uint64_shift_right(x_119, x_120);
x_122 = lean_uint64_xor(x_119, x_121);
x_123 = 16;
x_124 = lean_uint64_shift_right(x_122, x_123);
x_125 = lean_uint64_xor(x_122, x_124);
x_126 = lean_uint64_to_usize(x_125);
x_127 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_128 = 1;
x_129 = lean_usize_sub(x_127, x_128);
x_130 = lean_usize_land(x_126, x_129);
x_131 = lean_array_uget(x_117, x_130);
lean_dec_ref(x_117);
x_132 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_131);
lean_dec(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; size_t x_155; size_t x_156; size_t x_157; lean_object* x_158; uint8_t x_159; 
lean_inc(x_1);
x_133 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_116);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_st_ref_take(x_2, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = lean_ctor_get(x_137, 1);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_137, 2);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_137, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 4);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_137, 5);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_137, 6);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_137, 7);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_137, 8);
lean_inc(x_147);
x_148 = lean_ctor_get(x_137, 9);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_137, 10);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_137, 11);
lean_inc_ref(x_150);
lean_dec(x_137);
x_151 = lean_ctor_get(x_138, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_152);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_153 = x_138;
} else {
 lean_dec_ref(x_138);
 x_153 = lean_box(0);
}
x_154 = lean_array_get_size(x_152);
x_155 = lean_usize_of_nat(x_154);
lean_dec(x_154);
x_156 = lean_usize_sub(x_155, x_128);
x_157 = lean_usize_land(x_126, x_156);
x_158 = lean_array_uget(x_152, x_157);
x_159 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_151, x_160);
lean_dec(x_151);
lean_inc(x_134);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_134);
lean_ctor_set(x_162, 2, x_158);
x_163 = lean_array_uset(x_152, x_157, x_162);
x_164 = lean_unsigned_to_nat(4u);
x_165 = lean_nat_mul(x_161, x_164);
x_166 = lean_unsigned_to_nat(3u);
x_167 = lean_nat_div(x_165, x_166);
lean_dec(x_165);
x_168 = lean_array_get_size(x_163);
x_169 = lean_nat_dec_le(x_167, x_168);
lean_dec(x_168);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_163);
if (lean_is_scalar(x_153)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_153;
}
lean_ctor_set(x_171, 0, x_161);
lean_ctor_set(x_171, 1, x_170);
x_4 = x_134;
x_5 = x_139;
x_6 = x_140;
x_7 = x_141;
x_8 = x_142;
x_9 = x_143;
x_10 = x_144;
x_11 = x_145;
x_12 = x_146;
x_13 = x_147;
x_14 = x_148;
x_15 = x_149;
x_16 = x_150;
x_17 = x_171;
goto block_24;
}
else
{
lean_object* x_172; 
if (lean_is_scalar(x_153)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_153;
}
lean_ctor_set(x_172, 0, x_161);
lean_ctor_set(x_172, 1, x_163);
x_4 = x_134;
x_5 = x_139;
x_6 = x_140;
x_7 = x_141;
x_8 = x_142;
x_9 = x_143;
x_10 = x_144;
x_11 = x_145;
x_12 = x_146;
x_13 = x_147;
x_14 = x_148;
x_15 = x_149;
x_16 = x_150;
x_17 = x_172;
goto block_24;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_box(0);
x_174 = lean_array_uset(x_152, x_157, x_173);
lean_inc(x_134);
x_175 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_134, x_158);
x_176 = lean_array_uset(x_174, x_157, x_175);
if (lean_is_scalar(x_153)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_153;
}
lean_ctor_set(x_177, 0, x_151);
lean_ctor_set(x_177, 1, x_176);
x_4 = x_134;
x_5 = x_139;
x_6 = x_140;
x_7 = x_141;
x_8 = x_142;
x_9 = x_143;
x_10 = x_144;
x_11 = x_145;
x_12 = x_146;
x_13 = x_147;
x_14 = x_148;
x_15 = x_149;
x_16 = x_150;
x_17 = x_177;
goto block_24;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_1);
x_178 = lean_ctor_get(x_132, 0);
lean_inc(x_178);
lean_dec_ref(x_132);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_116);
return x_179;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevel___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_collectLevel___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_collectLevel(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_5, x_8);
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_check(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_preprocess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 8, x_12);
x_13 = lean_st_ref_set(x_1, x_7, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 8);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1;
x_18 = lean_name_append_index_after(x_17, x_16);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_4, 8);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1;
x_22 = lean_name_append_index_after(x_21, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
x_27 = lean_ctor_get(x_7, 3);
x_28 = lean_ctor_get(x_7, 4);
x_29 = lean_ctor_get(x_7, 5);
x_30 = lean_ctor_get(x_7, 6);
x_31 = lean_ctor_get(x_7, 7);
x_32 = lean_ctor_get(x_7, 8);
x_33 = lean_ctor_get(x_7, 9);
x_34 = lean_ctor_get(x_7, 10);
x_35 = lean_ctor_get(x_7, 11);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_32, x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_29);
lean_ctor_set(x_38, 6, x_30);
lean_ctor_set(x_38, 7, x_31);
lean_ctor_set(x_38, 8, x_37);
lean_ctor_set(x_38, 9, x_33);
lean_ctor_set(x_38, 10, x_34);
lean_ctor_set(x_38, 11, x_35);
x_39 = lean_st_ref_set(x_1, x_38, x_8);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_4, 8);
lean_inc(x_42);
lean_dec(x_4);
x_43 = l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1;
x_44 = lean_name_append_index_after(x_43, x_42);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Meta_Closure_mkNextUserName(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 11);
x_9 = lean_array_push(x_8, x_1);
lean_ctor_set(x_5, 11, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
x_25 = lean_ctor_get(x_5, 8);
x_26 = lean_ctor_get(x_5, 9);
x_27 = lean_ctor_get(x_5, 10);
x_28 = lean_ctor_get(x_5, 11);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_22);
lean_ctor_set(x_30, 6, x_23);
lean_ctor_set(x_30, 7, x_24);
lean_ctor_set(x_30, 8, x_25);
lean_ctor_set(x_30, 9, x_26);
lean_ctor_set(x_30, 10, x_27);
lean_ctor_set(x_30, 11, x_29);
x_31 = lean_st_ref_set(x_2, x_30, x_6);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushToProcess___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pushToProcess___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_pushToProcess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_ExprStructEq_beq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_ExprStructEq_beq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_ExprStructEq_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
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
x_26 = l_Lean_ExprStructEq_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_ExprStructEq_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = l_Lean_ExprStructEq_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(x_2);
x_12 = lean_apply_9(x_1, x_4, x_5, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_7);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(x_1, x_2, x_14, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_Meta_Closure_collectLevel___redArg(x_8, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_12;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l_Lean_Meta_Closure_collectLevel___redArg(x_14, x_3, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
x_1 = x_15;
x_2 = x_19;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg(x_1, x_2, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_186; 
x_186 = l_Lean_Expr_hasLevelParam(x_1);
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = l_Lean_Expr_hasFVar(x_1);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_1);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_8);
return x_189;
}
else
{
goto block_185;
}
}
else
{
goto block_185;
}
}
else
{
goto block_185;
}
block_29:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_10);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_16);
lean_ctor_set(x_23, 7, x_12);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_13);
lean_ctor_set(x_23, 10, x_17);
lean_ctor_set(x_23, 11, x_19);
x_24 = lean_st_ref_set(x_3, x_23, x_9);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
block_185:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_st_ref_get(x_3, x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_32);
lean_dec(x_31);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_32);
x_37 = lean_array_get_size(x_36);
x_38 = l_Lean_ExprStructEq_hash(x_1);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
lean_dec_ref(x_36);
x_51 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_1, x_50);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_free_object(x_30);
lean_inc(x_3);
lean_inc_ref(x_1);
x_52 = l_Lean_Meta_Closure_collectExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_st_ref_take(x_3, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec_ref(x_55);
x_59 = lean_ctor_get(x_56, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_56, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_56, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_56, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_56, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 9);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_56, 10);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_56, 11);
lean_inc_ref(x_69);
lean_dec(x_56);
x_70 = !lean_is_exclusive(x_57);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
x_73 = lean_array_get_size(x_72);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = lean_usize_sub(x_74, x_47);
x_76 = lean_usize_land(x_45, x_75);
x_77 = lean_array_uget(x_72, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_71, x_79);
lean_dec(x_71);
lean_inc(x_53);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_53);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_array_uset(x_72, x_76, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_82);
lean_ctor_set(x_57, 1, x_89);
lean_ctor_set(x_57, 0, x_80);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_57;
goto block_29;
}
else
{
lean_ctor_set(x_57, 1, x_82);
lean_ctor_set(x_57, 0, x_80);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_57;
goto block_29;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_box(0);
x_91 = lean_array_uset(x_72, x_76, x_90);
lean_inc(x_53);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_1, x_53, x_77);
x_93 = lean_array_uset(x_91, x_76, x_92);
lean_ctor_set(x_57, 1, x_93);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_57;
goto block_29;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; size_t x_99; lean_object* x_100; uint8_t x_101; 
x_94 = lean_ctor_get(x_57, 0);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_57);
x_96 = lean_array_get_size(x_95);
x_97 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_98 = lean_usize_sub(x_97, x_47);
x_99 = lean_usize_land(x_45, x_98);
x_100 = lean_array_uget(x_95, x_99);
x_101 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_1, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_94, x_102);
lean_dec(x_94);
lean_inc(x_53);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_53);
lean_ctor_set(x_104, 2, x_100);
x_105 = lean_array_uset(x_95, x_99, x_104);
x_106 = lean_unsigned_to_nat(4u);
x_107 = lean_nat_mul(x_103, x_106);
x_108 = lean_unsigned_to_nat(3u);
x_109 = lean_nat_div(x_107, x_108);
lean_dec(x_107);
x_110 = lean_array_get_size(x_105);
x_111 = lean_nat_dec_le(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_112);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_113;
goto block_29;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_103);
lean_ctor_set(x_114, 1, x_105);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_114;
goto block_29;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_box(0);
x_116 = lean_array_uset(x_95, x_99, x_115);
lean_inc(x_53);
x_117 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_1, x_53, x_100);
x_118 = lean_array_uset(x_116, x_99, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_94);
lean_ctor_set(x_119, 1, x_118);
x_9 = x_58;
x_10 = x_61;
x_11 = x_63;
x_12 = x_65;
x_13 = x_67;
x_14 = x_66;
x_15 = x_53;
x_16 = x_64;
x_17 = x_68;
x_18 = x_60;
x_19 = x_69;
x_20 = x_62;
x_21 = x_59;
x_22 = x_119;
goto block_29;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_52;
}
}
else
{
lean_object* x_120; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_51, 0);
lean_inc(x_120);
lean_dec_ref(x_51);
lean_ctor_set(x_30, 0, x_120);
return x_30;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; size_t x_131; size_t x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; lean_object* x_137; 
x_121 = lean_ctor_get(x_30, 1);
lean_inc(x_121);
lean_dec(x_30);
x_122 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_122);
lean_dec_ref(x_32);
x_123 = lean_array_get_size(x_122);
x_124 = l_Lean_ExprStructEq_hash(x_1);
x_125 = 32;
x_126 = lean_uint64_shift_right(x_124, x_125);
x_127 = lean_uint64_xor(x_124, x_126);
x_128 = 16;
x_129 = lean_uint64_shift_right(x_127, x_128);
x_130 = lean_uint64_xor(x_127, x_129);
x_131 = lean_uint64_to_usize(x_130);
x_132 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_133 = 1;
x_134 = lean_usize_sub(x_132, x_133);
x_135 = lean_usize_land(x_131, x_134);
x_136 = lean_array_uget(x_122, x_135);
lean_dec_ref(x_122);
x_137 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_1, x_136);
lean_dec(x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_138 = l_Lean_Meta_Closure_collectExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_121);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; size_t x_160; size_t x_161; size_t x_162; lean_object* x_163; uint8_t x_164; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec_ref(x_138);
x_141 = lean_st_ref_take(x_3, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec_ref(x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_142, 2);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_142, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_142, 4);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_142, 5);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_142, 6);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_142, 7);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_142, 8);
lean_inc(x_152);
x_153 = lean_ctor_get(x_142, 9);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_142, 10);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_142, 11);
lean_inc_ref(x_155);
lean_dec(x_142);
x_156 = lean_ctor_get(x_143, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_143, 1);
lean_inc_ref(x_157);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_158 = x_143;
} else {
 lean_dec_ref(x_143);
 x_158 = lean_box(0);
}
x_159 = lean_array_get_size(x_157);
x_160 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_161 = lean_usize_sub(x_160, x_133);
x_162 = lean_usize_land(x_131, x_161);
x_163 = lean_array_uget(x_157, x_162);
x_164 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_1, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_add(x_156, x_165);
lean_dec(x_156);
lean_inc(x_139);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_1);
lean_ctor_set(x_167, 1, x_139);
lean_ctor_set(x_167, 2, x_163);
x_168 = lean_array_uset(x_157, x_162, x_167);
x_169 = lean_unsigned_to_nat(4u);
x_170 = lean_nat_mul(x_166, x_169);
x_171 = lean_unsigned_to_nat(3u);
x_172 = lean_nat_div(x_170, x_171);
lean_dec(x_170);
x_173 = lean_array_get_size(x_168);
x_174 = lean_nat_dec_le(x_172, x_173);
lean_dec(x_173);
lean_dec(x_172);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_168);
if (lean_is_scalar(x_158)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_158;
}
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_175);
x_9 = x_144;
x_10 = x_147;
x_11 = x_149;
x_12 = x_151;
x_13 = x_153;
x_14 = x_152;
x_15 = x_139;
x_16 = x_150;
x_17 = x_154;
x_18 = x_146;
x_19 = x_155;
x_20 = x_148;
x_21 = x_145;
x_22 = x_176;
goto block_29;
}
else
{
lean_object* x_177; 
if (lean_is_scalar(x_158)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_158;
}
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_168);
x_9 = x_144;
x_10 = x_147;
x_11 = x_149;
x_12 = x_151;
x_13 = x_153;
x_14 = x_152;
x_15 = x_139;
x_16 = x_150;
x_17 = x_154;
x_18 = x_146;
x_19 = x_155;
x_20 = x_148;
x_21 = x_145;
x_22 = x_177;
goto block_29;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_box(0);
x_179 = lean_array_uset(x_157, x_162, x_178);
lean_inc(x_139);
x_180 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_1, x_139, x_163);
x_181 = lean_array_uset(x_179, x_162, x_180);
if (lean_is_scalar(x_158)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_158;
}
lean_ctor_set(x_182, 0, x_156);
lean_ctor_set(x_182, 1, x_181);
x_9 = x_144;
x_10 = x_147;
x_11 = x_149;
x_12 = x_151;
x_13 = x_153;
x_14 = x_152;
x_15 = x_139;
x_16 = x_150;
x_17 = x_154;
x_18 = x_146;
x_19 = x_155;
x_20 = x_148;
x_21 = x_145;
x_22 = x_182;
goto block_29;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_138;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_137, 0);
lean_inc(x_183);
lean_dec_ref(x_137);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_121);
return x_184;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = l_Lean_mkAppN(x_1, x_2);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_12, x_13, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = 0;
lean_inc_ref(x_4);
lean_inc(x_9);
x_11 = l_Lean_FVarId_getValue_x3f___redArg(x_9, x_10, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
if (x_2 == 0)
{
lean_dec(x_12);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
goto block_39;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
goto block_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec_ref(x_12);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_41 = l_Lean_Meta_Closure_preprocess(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
return x_44;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_41;
}
}
}
block_39:
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6(x_14, x_15, x_16, x_17, x_18, x_19, x_13);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_20, 0, x_9);
x_24 = l_Lean_Meta_Closure_pushToProcess___redArg(x_20, x_15, x_23);
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lean_mkFVar(x_22);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_mkFVar(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
lean_inc(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_Closure_pushToProcess___redArg(x_33, x_15, x_32);
lean_dec(x_15);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Lean_mkFVar(x_31);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_inc(x_49);
x_50 = l_Lean_MVarId_getDecl(x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_53);
lean_dec(x_51);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_53);
x_54 = l_Lean_Meta_Closure_preprocess(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_57 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_113; lean_object* x_114; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_3, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_113 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg(x_49, x_5, x_65);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec_ref(x_53);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_66 = x_1;
x_67 = x_3;
x_68 = x_115;
goto block_112;
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_114, 0);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_dec_ref(x_113);
x_119 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_119);
lean_dec(x_117);
x_120 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(x_120, 0, x_1);
x_121 = lean_array_get_size(x_119);
lean_dec_ref(x_119);
lean_ctor_set(x_114, 0, x_121);
x_122 = 0;
lean_inc(x_3);
x_123 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(x_53, x_114, x_120, x_122, x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_66 = x_124;
x_67 = x_3;
x_68 = x_125;
goto block_112;
}
else
{
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_3);
return x_123;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec(x_114);
x_127 = lean_ctor_get(x_113, 1);
lean_inc(x_127);
lean_dec_ref(x_113);
x_128 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_128);
lean_dec(x_126);
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(x_129, 0, x_1);
x_130 = lean_array_get_size(x_128);
lean_dec_ref(x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = 0;
lean_inc(x_3);
x_133 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(x_53, x_131, x_129, x_132, x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_127);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_66 = x_134;
x_67 = x_3;
x_68 = x_135;
goto block_112;
}
else
{
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_3);
return x_133;
}
}
}
block_112:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_st_ref_take(x_67, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_ctor_get(x_70, 6);
x_74 = lean_ctor_get(x_70, 9);
x_75 = lean_unsigned_to_nat(0u);
x_76 = 0;
x_77 = 0;
lean_inc(x_61);
x_78 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_61);
lean_ctor_set(x_78, 2, x_64);
lean_ctor_set(x_78, 3, x_58);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*4 + 1, x_77);
x_79 = lean_array_push(x_73, x_78);
x_80 = lean_array_push(x_74, x_66);
lean_ctor_set(x_70, 9, x_80);
lean_ctor_set(x_70, 6, x_79);
x_81 = lean_st_ref_set(x_67, x_70, x_71);
lean_dec(x_67);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = l_Lean_mkFVar(x_61);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = l_Lean_mkFVar(x_61);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_88 = lean_ctor_get(x_70, 0);
x_89 = lean_ctor_get(x_70, 1);
x_90 = lean_ctor_get(x_70, 2);
x_91 = lean_ctor_get(x_70, 3);
x_92 = lean_ctor_get(x_70, 4);
x_93 = lean_ctor_get(x_70, 5);
x_94 = lean_ctor_get(x_70, 6);
x_95 = lean_ctor_get(x_70, 7);
x_96 = lean_ctor_get(x_70, 8);
x_97 = lean_ctor_get(x_70, 9);
x_98 = lean_ctor_get(x_70, 10);
x_99 = lean_ctor_get(x_70, 11);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_70);
x_100 = lean_unsigned_to_nat(0u);
x_101 = 0;
x_102 = 0;
lean_inc(x_61);
x_103 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_61);
lean_ctor_set(x_103, 2, x_64);
lean_ctor_set(x_103, 3, x_58);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4 + 1, x_102);
x_104 = lean_array_push(x_94, x_103);
x_105 = lean_array_push(x_97, x_66);
x_106 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_106, 0, x_88);
lean_ctor_set(x_106, 1, x_89);
lean_ctor_set(x_106, 2, x_90);
lean_ctor_set(x_106, 3, x_91);
lean_ctor_set(x_106, 4, x_92);
lean_ctor_set(x_106, 5, x_93);
lean_ctor_set(x_106, 6, x_104);
lean_ctor_set(x_106, 7, x_95);
lean_ctor_set(x_106, 8, x_96);
lean_ctor_set(x_106, 9, x_105);
lean_ctor_set(x_106, 10, x_98);
lean_ctor_set(x_106, 11, x_99);
x_107 = lean_st_ref_set(x_67, x_106, x_71);
lean_dec(x_67);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = l_Lean_mkFVar(x_61);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
}
else
{
lean_dec_ref(x_53);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_57;
}
}
else
{
lean_dec_ref(x_53);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_54;
}
}
else
{
uint8_t x_136; 
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_50);
if (x_136 == 0)
{
return x_50;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_50, 0);
x_138 = lean_ctor_get(x_50, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_50);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
case 3:
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_140 = lean_ctor_get(x_1, 0);
lean_inc(x_140);
x_141 = l_Lean_Meta_Closure_collectLevel___redArg(x_140, x_3, x_8);
lean_dec(x_3);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_1, x_143);
lean_dec_ref(x_1);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_141);
x_147 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_1, x_145);
lean_dec_ref(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
case 4:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_149 = lean_ctor_get(x_1, 1);
lean_inc(x_149);
x_150 = lean_box(0);
x_151 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg(x_149, x_150, x_3, x_8);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(x_1, x_153);
lean_ctor_set(x_151, 0, x_154);
return x_151;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_151, 0);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_151);
x_157 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(x_1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
case 5:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_160);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_161 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_160, x_2, x_3, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_1, x_162, x_166);
lean_dec_ref(x_1);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_1, x_162, x_168);
lean_dec_ref(x_1);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_dec(x_162);
lean_dec_ref(x_1);
return x_164;
}
}
else
{
lean_dec_ref(x_160);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_161;
}
}
case 6:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_174);
x_175 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_173);
x_176 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
lean_inc_ref(x_174);
x_179 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; size_t x_191; size_t x_192; uint8_t x_193; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_191 = lean_ptr_addr(x_173);
lean_dec_ref(x_173);
x_192 = lean_ptr_addr(x_177);
x_193 = lean_usize_dec_eq(x_191, x_192);
if (x_193 == 0)
{
lean_dec_ref(x_174);
x_183 = x_193;
goto block_190;
}
else
{
size_t x_194; size_t x_195; uint8_t x_196; 
x_194 = lean_ptr_addr(x_174);
lean_dec_ref(x_174);
x_195 = lean_ptr_addr(x_180);
x_196 = lean_usize_dec_eq(x_194, x_195);
x_183 = x_196;
goto block_190;
}
block_190:
{
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec_ref(x_1);
x_184 = l_Lean_Expr_lam___override(x_172, x_177, x_180, x_175);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_182;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_181);
return x_185;
}
else
{
uint8_t x_186; 
x_186 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_175, x_175);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_1);
x_187 = l_Lean_Expr_lam___override(x_172, x_177, x_180, x_175);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
else
{
lean_object* x_189; 
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_172);
if (lean_is_scalar(x_182)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_182;
}
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_181);
return x_189;
}
}
}
}
else
{
lean_dec(x_177);
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_1);
return x_179;
}
}
else
{
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_176;
}
}
case 7:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_1, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_199);
x_200 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_198);
x_201 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_198, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
lean_inc_ref(x_199);
x_204 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; size_t x_216; size_t x_217; uint8_t x_218; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_216 = lean_ptr_addr(x_198);
lean_dec_ref(x_198);
x_217 = lean_ptr_addr(x_202);
x_218 = lean_usize_dec_eq(x_216, x_217);
if (x_218 == 0)
{
lean_dec_ref(x_199);
x_208 = x_218;
goto block_215;
}
else
{
size_t x_219; size_t x_220; uint8_t x_221; 
x_219 = lean_ptr_addr(x_199);
lean_dec_ref(x_199);
x_220 = lean_ptr_addr(x_205);
x_221 = lean_usize_dec_eq(x_219, x_220);
x_208 = x_221;
goto block_215;
}
block_215:
{
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
lean_dec_ref(x_1);
x_209 = l_Lean_Expr_forallE___override(x_197, x_202, x_205, x_200);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_207;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
return x_210;
}
else
{
uint8_t x_211; 
x_211 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_200, x_200);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec_ref(x_1);
x_212 = l_Lean_Expr_forallE___override(x_197, x_202, x_205, x_200);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_207;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_206);
return x_213;
}
else
{
lean_object* x_214; 
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_197);
if (lean_is_scalar(x_207)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_207;
}
lean_ctor_set(x_214, 0, x_1);
lean_ctor_set(x_214, 1, x_206);
return x_214;
}
}
}
}
else
{
lean_dec(x_202);
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_1);
return x_204;
}
}
else
{
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_201;
}
}
case 8:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_225);
x_226 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_223);
x_227 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec_ref(x_227);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_224);
x_230 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec_ref(x_230);
lean_inc_ref(x_225);
x_233 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; size_t x_247; size_t x_248; uint8_t x_249; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
x_247 = lean_ptr_addr(x_223);
lean_dec_ref(x_223);
x_248 = lean_ptr_addr(x_228);
x_249 = lean_usize_dec_eq(x_247, x_248);
if (x_249 == 0)
{
lean_dec_ref(x_224);
x_237 = x_249;
goto block_246;
}
else
{
size_t x_250; size_t x_251; uint8_t x_252; 
x_250 = lean_ptr_addr(x_224);
lean_dec_ref(x_224);
x_251 = lean_ptr_addr(x_231);
x_252 = lean_usize_dec_eq(x_250, x_251);
x_237 = x_252;
goto block_246;
}
block_246:
{
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec_ref(x_225);
lean_dec_ref(x_1);
x_238 = l_Lean_Expr_letE___override(x_222, x_228, x_231, x_234, x_226);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_235);
return x_239;
}
else
{
size_t x_240; size_t x_241; uint8_t x_242; 
x_240 = lean_ptr_addr(x_225);
lean_dec_ref(x_225);
x_241 = lean_ptr_addr(x_234);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_1);
x_243 = l_Lean_Expr_letE___override(x_222, x_228, x_231, x_234, x_226);
if (lean_is_scalar(x_236)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_236;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_235);
return x_244;
}
else
{
lean_object* x_245; 
lean_dec(x_234);
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_222);
if (lean_is_scalar(x_236)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_236;
}
lean_ctor_set(x_245, 0, x_1);
lean_ctor_set(x_245, 1, x_235);
return x_245;
}
}
}
}
else
{
lean_dec(x_231);
lean_dec(x_228);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_1);
return x_233;
}
}
else
{
lean_dec(x_228);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_230;
}
}
else
{
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_227;
}
}
case 10:
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_253);
x_254 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_253, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_1, x_256);
lean_ctor_set(x_254, 0, x_257);
return x_254;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_254, 0);
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_254);
x_260 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_1, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_dec_ref(x_1);
return x_254;
}
}
case 11:
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_262);
x_263 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_262, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_1, x_265);
lean_ctor_set(x_263, 0, x_266);
return x_263;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_263, 0);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_263);
x_269 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_1, x_267);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_dec_ref(x_1);
return x_263;
}
}
default: 
{
lean_object* x_271; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_1);
lean_ctor_set(x_271, 1, x_8);
return x_271;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6_spec__6(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__6(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__8(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___redArg(x_1, x_2, x_3, x_13, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = lean_unbox(x_7);
x_17 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__9(x_1, x_2, x_3, x_4, x_14, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__10(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_Closure_collectExprAux___lam__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_30 = l_Lean_Meta_Closure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_189; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_189 = l_Lean_Expr_hasLevelParam(x_31);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = l_Lean_Expr_hasFVar(x_31);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = l_Lean_Expr_hasMVar(x_31);
if (x_191 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_30;
}
else
{
lean_dec_ref(x_30);
goto block_188;
}
}
else
{
lean_dec_ref(x_30);
goto block_188;
}
}
else
{
lean_dec_ref(x_30);
goto block_188;
}
block_188:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_st_ref_get(x_3, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_35);
lean_dec(x_34);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_35);
x_40 = lean_array_get_size(x_39);
x_41 = l_Lean_ExprStructEq_hash(x_31);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_39, x_52);
lean_dec_ref(x_39);
x_54 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_31, x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_free_object(x_33);
lean_inc(x_3);
lean_inc(x_31);
x_55 = l_Lean_Meta_Closure_collectExprAux(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_3, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_59, 5);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_59, 7);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_59, 8);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 9);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_59, 10);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_59, 11);
lean_inc_ref(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
x_76 = lean_array_get_size(x_75);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_50);
x_79 = lean_usize_land(x_48, x_78);
x_80 = lean_array_uget(x_75, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_31, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_74, x_82);
lean_dec(x_74);
lean_inc(x_56);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_31);
lean_ctor_set(x_84, 1, x_56);
lean_ctor_set(x_84, 2, x_80);
x_85 = lean_array_uset(x_75, x_79, x_84);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_nat_mul(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_85);
lean_ctor_set(x_60, 1, x_92);
lean_ctor_set(x_60, 0, x_83);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_60;
goto block_29;
}
else
{
lean_ctor_set(x_60, 1, x_85);
lean_ctor_set(x_60, 0, x_83);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_60;
goto block_29;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_75, x_79, x_93);
lean_inc(x_56);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_31, x_56, x_80);
x_96 = lean_array_uset(x_94, x_79, x_95);
lean_ctor_set(x_60, 1, x_96);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_60;
goto block_29;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
x_97 = lean_ctor_get(x_60, 0);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_60);
x_99 = lean_array_get_size(x_98);
x_100 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_101 = lean_usize_sub(x_100, x_50);
x_102 = lean_usize_land(x_48, x_101);
x_103 = lean_array_uget(x_98, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_31, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_97, x_105);
lean_dec(x_97);
lean_inc(x_56);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_31);
lean_ctor_set(x_107, 1, x_56);
lean_ctor_set(x_107, 2, x_103);
x_108 = lean_array_uset(x_98, x_102, x_107);
x_109 = lean_unsigned_to_nat(4u);
x_110 = lean_nat_mul(x_106, x_109);
x_111 = lean_unsigned_to_nat(3u);
x_112 = lean_nat_div(x_110, x_111);
lean_dec(x_110);
x_113 = lean_array_get_size(x_108);
x_114 = lean_nat_dec_le(x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_108);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_106);
lean_ctor_set(x_116, 1, x_115);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_116;
goto block_29;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_108);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_117;
goto block_29;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_box(0);
x_119 = lean_array_uset(x_98, x_102, x_118);
lean_inc(x_56);
x_120 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_31, x_56, x_103);
x_121 = lean_array_uset(x_119, x_102, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_97);
lean_ctor_set(x_122, 1, x_121);
x_9 = x_66;
x_10 = x_61;
x_11 = x_62;
x_12 = x_68;
x_13 = x_65;
x_14 = x_63;
x_15 = x_71;
x_16 = x_72;
x_17 = x_64;
x_18 = x_69;
x_19 = x_70;
x_20 = x_67;
x_21 = x_56;
x_22 = x_122;
goto block_29;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_3);
return x_55;
}
}
else
{
lean_object* x_123; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_123 = lean_ctor_get(x_54, 0);
lean_inc(x_123);
lean_dec_ref(x_54);
lean_ctor_set(x_33, 0, x_123);
return x_33;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; size_t x_134; size_t x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; 
x_124 = lean_ctor_get(x_33, 1);
lean_inc(x_124);
lean_dec(x_33);
x_125 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_125);
lean_dec_ref(x_35);
x_126 = lean_array_get_size(x_125);
x_127 = l_Lean_ExprStructEq_hash(x_31);
x_128 = 32;
x_129 = lean_uint64_shift_right(x_127, x_128);
x_130 = lean_uint64_xor(x_127, x_129);
x_131 = 16;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = lean_uint64_to_usize(x_133);
x_135 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_136 = 1;
x_137 = lean_usize_sub(x_135, x_136);
x_138 = lean_usize_land(x_134, x_137);
x_139 = lean_array_uget(x_125, x_138);
lean_dec_ref(x_125);
x_140 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectExprAux_spec__0___redArg(x_31, x_139);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_inc(x_3);
lean_inc(x_31);
x_141 = l_Lean_Meta_Closure_collectExprAux(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; size_t x_163; size_t x_164; size_t x_165; lean_object* x_166; uint8_t x_167; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_st_ref_take(x_3, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 1);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec_ref(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_145, 2);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_145, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 4);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_145, 5);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_145, 6);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_145, 7);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_145, 8);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 9);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_145, 10);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_145, 11);
lean_inc_ref(x_158);
lean_dec(x_145);
x_159 = lean_ctor_get(x_146, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_146, 1);
lean_inc_ref(x_160);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_161 = x_146;
} else {
 lean_dec_ref(x_146);
 x_161 = lean_box(0);
}
x_162 = lean_array_get_size(x_160);
x_163 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_164 = lean_usize_sub(x_163, x_136);
x_165 = lean_usize_land(x_134, x_164);
x_166 = lean_array_uget(x_160, x_165);
x_167 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectExprAux_spec__1___redArg(x_31, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_add(x_159, x_168);
lean_dec(x_159);
lean_inc(x_142);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_31);
lean_ctor_set(x_170, 1, x_142);
lean_ctor_set(x_170, 2, x_166);
x_171 = lean_array_uset(x_160, x_165, x_170);
x_172 = lean_unsigned_to_nat(4u);
x_173 = lean_nat_mul(x_169, x_172);
x_174 = lean_unsigned_to_nat(3u);
x_175 = lean_nat_div(x_173, x_174);
lean_dec(x_173);
x_176 = lean_array_get_size(x_171);
x_177 = lean_nat_dec_le(x_175, x_176);
lean_dec(x_176);
lean_dec(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_171);
if (lean_is_scalar(x_161)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_161;
}
lean_ctor_set(x_179, 0, x_169);
lean_ctor_set(x_179, 1, x_178);
x_9 = x_152;
x_10 = x_147;
x_11 = x_148;
x_12 = x_154;
x_13 = x_151;
x_14 = x_149;
x_15 = x_157;
x_16 = x_158;
x_17 = x_150;
x_18 = x_155;
x_19 = x_156;
x_20 = x_153;
x_21 = x_142;
x_22 = x_179;
goto block_29;
}
else
{
lean_object* x_180; 
if (lean_is_scalar(x_161)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_161;
}
lean_ctor_set(x_180, 0, x_169);
lean_ctor_set(x_180, 1, x_171);
x_9 = x_152;
x_10 = x_147;
x_11 = x_148;
x_12 = x_154;
x_13 = x_151;
x_14 = x_149;
x_15 = x_157;
x_16 = x_158;
x_17 = x_150;
x_18 = x_155;
x_19 = x_156;
x_20 = x_153;
x_21 = x_142;
x_22 = x_180;
goto block_29;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_box(0);
x_182 = lean_array_uset(x_160, x_165, x_181);
lean_inc(x_142);
x_183 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectExprAux_spec__5___redArg(x_31, x_142, x_166);
x_184 = lean_array_uset(x_182, x_165, x_183);
if (lean_is_scalar(x_161)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_161;
}
lean_ctor_set(x_185, 0, x_159);
lean_ctor_set(x_185, 1, x_184);
x_9 = x_152;
x_10 = x_147;
x_11 = x_148;
x_12 = x_154;
x_13 = x_151;
x_14 = x_149;
x_15 = x_157;
x_16 = x_158;
x_17 = x_150;
x_18 = x_155;
x_19 = x_156;
x_20 = x_153;
x_21 = x_142;
x_22 = x_185;
goto block_29;
}
}
else
{
lean_dec(x_31);
lean_dec(x_3);
return x_141;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_186 = lean_ctor_get(x_140, 0);
lean_inc(x_186);
lean_dec_ref(x_140);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_124);
return x_187;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_30;
}
block_29:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_9);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_12);
lean_ctor_set(x_23, 8, x_18);
lean_ctor_set(x_23, 9, x_19);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
x_24 = lean_st_ref_set(x_3, x_23, x_10);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_collectExpr(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_fget(x_3, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc_ref(x_1);
x_11 = l_Lean_LocalContext_get_x21(x_1, x_8);
x_12 = l_Lean_LocalDecl_index(x_11);
lean_dec_ref(x_11);
lean_inc_ref(x_1);
x_13 = l_Lean_LocalContext_get_x21(x_1, x_10);
x_14 = l_Lean_LocalDecl_index(x_13);
lean_dec_ref(x_13);
x_15 = lean_nat_dec_lt(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_9);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_4);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
x_4 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 11);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l_Array_isEmpty___redArg(x_8);
lean_dec_ref(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_4);
x_10 = lean_st_ref_take(x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_11, 11);
x_16 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_17 = l_Array_back_x21___redArg(x_16, x_15);
x_18 = lean_array_pop(x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Meta_Closure_pickNextToProcessAux(x_13, x_19, x_18, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_11, 11, x_22);
x_23 = lean_st_ref_set(x_1, x_11, x_12);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
x_32 = lean_ctor_get(x_11, 2);
x_33 = lean_ctor_get(x_11, 3);
x_34 = lean_ctor_get(x_11, 4);
x_35 = lean_ctor_get(x_11, 5);
x_36 = lean_ctor_get(x_11, 6);
x_37 = lean_ctor_get(x_11, 7);
x_38 = lean_ctor_get(x_11, 8);
x_39 = lean_ctor_get(x_11, 9);
x_40 = lean_ctor_get(x_11, 10);
x_41 = lean_ctor_get(x_11, 11);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_42 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_43 = l_Array_back_x21___redArg(x_42, x_41);
x_44 = lean_array_pop(x_41);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Meta_Closure_pickNextToProcessAux(x_13, x_45, x_44, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_30);
lean_ctor_set(x_49, 1, x_31);
lean_ctor_set(x_49, 2, x_32);
lean_ctor_set(x_49, 3, x_33);
lean_ctor_set(x_49, 4, x_34);
lean_ctor_set(x_49, 5, x_35);
lean_ctor_set(x_49, 6, x_36);
lean_ctor_set(x_49, 7, x_37);
lean_ctor_set(x_49, 8, x_38);
lean_ctor_set(x_49, 9, x_39);
lean_ctor_set(x_49, 10, x_40);
lean_ctor_set(x_49, 11, x_48);
x_50 = lean_st_ref_set(x_1, x_49, x_12);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_47);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec_ref(x_2);
x_55 = lean_box(0);
lean_ctor_set(x_4, 0, x_55);
return x_4;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_58 = lean_ctor_get(x_56, 11);
lean_inc_ref(x_58);
lean_dec(x_56);
x_59 = l_Array_isEmpty___redArg(x_58);
lean_dec_ref(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_60 = lean_st_ref_take(x_1, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_63);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_61, 2);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_61, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 4);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_61, 5);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_61, 6);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_61, 7);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_61, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 9);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_61, 10);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_61, 11);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 lean_ctor_release(x_61, 7);
 lean_ctor_release(x_61, 8);
 lean_ctor_release(x_61, 9);
 lean_ctor_release(x_61, 10);
 lean_ctor_release(x_61, 11);
 x_76 = x_61;
} else {
 lean_dec_ref(x_61);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_78 = l_Array_back_x21___redArg(x_77, x_75);
x_79 = lean_array_pop(x_75);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Lean_Meta_Closure_pickNextToProcessAux(x_63, x_80, x_79, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 12, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_64);
lean_ctor_set(x_84, 1, x_65);
lean_ctor_set(x_84, 2, x_66);
lean_ctor_set(x_84, 3, x_67);
lean_ctor_set(x_84, 4, x_68);
lean_ctor_set(x_84, 5, x_69);
lean_ctor_set(x_84, 6, x_70);
lean_ctor_set(x_84, 7, x_71);
lean_ctor_set(x_84, 8, x_72);
lean_ctor_set(x_84, 9, x_73);
lean_ctor_set(x_84, 10, x_74);
lean_ctor_set(x_84, 11, x_83);
x_85 = lean_st_ref_set(x_1, x_84, x_62);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_82);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_2);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_57);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_2, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 10);
x_9 = lean_array_push(x_8, x_1);
lean_ctor_set(x_5, 10, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
x_25 = lean_ctor_get(x_5, 8);
x_26 = lean_ctor_get(x_5, 9);
x_27 = lean_ctor_get(x_5, 10);
x_28 = lean_ctor_get(x_5, 11);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_29 = lean_array_push(x_27, x_1);
x_30 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_22);
lean_ctor_set(x_30, 6, x_23);
lean_ctor_set(x_30, 7, x_24);
lean_ctor_set(x_30, 8, x_25);
lean_ctor_set(x_30, 9, x_26);
lean_ctor_set(x_30, 10, x_29);
lean_ctor_set(x_30, 11, x_28);
x_31 = lean_st_ref_set(x_2, x_30, x_6);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Closure_pushFVarArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_22, sizeof(void*)*4 + 1, x_21);
x_23 = lean_array_push(x_19, x_22);
lean_ctor_set(x_16, 5, x_23);
x_24 = lean_st_ref_set(x_6, x_16, x_17);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 2);
x_34 = lean_ctor_get(x_16, 3);
x_35 = lean_ctor_get(x_16, 4);
x_36 = lean_ctor_get(x_16, 5);
x_37 = lean_ctor_get(x_16, 6);
x_38 = lean_ctor_get(x_16, 7);
x_39 = lean_ctor_get(x_16, 8);
x_40 = lean_ctor_get(x_16, 9);
x_41 = lean_ctor_get(x_16, 10);
x_42 = lean_ctor_get(x_16, 11);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_43 = lean_unsigned_to_nat(0u);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_1);
lean_ctor_set(x_45, 2, x_2);
lean_ctor_set(x_45, 3, x_13);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_45, sizeof(void*)*4 + 1, x_44);
x_46 = lean_array_push(x_36, x_45);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_32);
lean_ctor_set(x_47, 2, x_33);
lean_ctor_set(x_47, 3, x_34);
lean_ctor_set(x_47, 4, x_35);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_47, 6, x_37);
lean_ctor_set(x_47, 7, x_38);
lean_ctor_set(x_47, 8, x_39);
lean_ctor_set(x_47, 9, x_40);
lean_ctor_set(x_47, 10, x_41);
lean_ctor_set(x_47, 11, x_42);
x_48 = lean_st_ref_set(x_6, x_47, x_17);
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
return x_12;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
x_13 = lean_unbox(x_5);
x_14 = l_Lean_Meta_Closure_pushLocalDecl(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_1);
x_10 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_2, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec_ref(x_9);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc_ref(x_3);
lean_inc(x_18);
x_20 = l_Lean_FVarId_getDecl___redArg(x_18, x_3, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 3);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec_ref(x_21);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_26 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_23, x_24, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_mkFVar(x_18);
x_29 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_28, x_2, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_7 = x_30;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_26;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec_ref(x_20);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
x_37 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_38 = lean_ctor_get(x_21, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_21, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_getZetaDeltaFVarIds___redArg(x_4, x_32);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
if (x_37 == 0)
{
uint8_t x_51; 
x_51 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(x_18, x_41);
lean_dec(x_41);
if (x_51 == 0)
{
lean_free_object(x_21);
lean_dec_ref(x_36);
goto block_50;
}
else
{
lean_object* x_52; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_52 = l_Lean_Meta_Closure_collectExpr(x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_55 = l_Lean_Meta_Closure_collectExpr(x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_2, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_ctor_get(x_59, 7);
x_63 = lean_unsigned_to_nat(0u);
x_64 = 0;
lean_inc(x_56);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_56);
lean_ctor_set(x_21, 3, x_53);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_63);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_64);
x_65 = lean_array_push(x_62, x_21);
lean_ctor_set(x_59, 7, x_65);
x_66 = lean_st_ref_set(x_2, x_59, x_60);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_st_ref_take(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_69, 5);
x_73 = lean_array_size(x_72);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_56, x_73, x_74, x_72);
lean_dec(x_56);
lean_ctor_set(x_69, 5, x_75);
x_76 = lean_st_ref_set(x_2, x_69, x_70);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_7 = x_77;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_79 = lean_ctor_get(x_69, 0);
x_80 = lean_ctor_get(x_69, 1);
x_81 = lean_ctor_get(x_69, 2);
x_82 = lean_ctor_get(x_69, 3);
x_83 = lean_ctor_get(x_69, 4);
x_84 = lean_ctor_get(x_69, 5);
x_85 = lean_ctor_get(x_69, 6);
x_86 = lean_ctor_get(x_69, 7);
x_87 = lean_ctor_get(x_69, 8);
x_88 = lean_ctor_get(x_69, 9);
x_89 = lean_ctor_get(x_69, 10);
x_90 = lean_ctor_get(x_69, 11);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_69);
x_91 = lean_array_size(x_84);
x_92 = 0;
x_93 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_56, x_91, x_92, x_84);
lean_dec(x_56);
x_94 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_80);
lean_ctor_set(x_94, 2, x_81);
lean_ctor_set(x_94, 3, x_82);
lean_ctor_set(x_94, 4, x_83);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_85);
lean_ctor_set(x_94, 7, x_86);
lean_ctor_set(x_94, 8, x_87);
lean_ctor_set(x_94, 9, x_88);
lean_ctor_set(x_94, 10, x_89);
lean_ctor_set(x_94, 11, x_90);
x_95 = lean_st_ref_set(x_2, x_94, x_70);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_7 = x_96;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_98 = lean_ctor_get(x_59, 0);
x_99 = lean_ctor_get(x_59, 1);
x_100 = lean_ctor_get(x_59, 2);
x_101 = lean_ctor_get(x_59, 3);
x_102 = lean_ctor_get(x_59, 4);
x_103 = lean_ctor_get(x_59, 5);
x_104 = lean_ctor_get(x_59, 6);
x_105 = lean_ctor_get(x_59, 7);
x_106 = lean_ctor_get(x_59, 8);
x_107 = lean_ctor_get(x_59, 9);
x_108 = lean_ctor_get(x_59, 10);
x_109 = lean_ctor_get(x_59, 11);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_59);
x_110 = lean_unsigned_to_nat(0u);
x_111 = 0;
lean_inc(x_56);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_56);
lean_ctor_set(x_21, 3, x_53);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_110);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_111);
x_112 = lean_array_push(x_105, x_21);
x_113 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_99);
lean_ctor_set(x_113, 2, x_100);
lean_ctor_set(x_113, 3, x_101);
lean_ctor_set(x_113, 4, x_102);
lean_ctor_set(x_113, 5, x_103);
lean_ctor_set(x_113, 6, x_104);
lean_ctor_set(x_113, 7, x_112);
lean_ctor_set(x_113, 8, x_106);
lean_ctor_set(x_113, 9, x_107);
lean_ctor_set(x_113, 10, x_108);
lean_ctor_set(x_113, 11, x_109);
x_114 = lean_st_ref_set(x_2, x_113, x_60);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = lean_st_ref_take(x_2, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_117, 2);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_117, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 4);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_117, 5);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_117, 6);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_117, 7);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_117, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_117, 9);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_117, 10);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_117, 11);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 lean_ctor_release(x_117, 6);
 lean_ctor_release(x_117, 7);
 lean_ctor_release(x_117, 8);
 lean_ctor_release(x_117, 9);
 lean_ctor_release(x_117, 10);
 lean_ctor_release(x_117, 11);
 x_131 = x_117;
} else {
 lean_dec_ref(x_117);
 x_131 = lean_box(0);
}
x_132 = lean_array_size(x_124);
x_133 = 0;
x_134 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_56, x_132, x_133, x_124);
lean_dec(x_56);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 12, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_119);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_122);
lean_ctor_set(x_135, 4, x_123);
lean_ctor_set(x_135, 5, x_134);
lean_ctor_set(x_135, 6, x_125);
lean_ctor_set(x_135, 7, x_126);
lean_ctor_set(x_135, 8, x_127);
lean_ctor_set(x_135, 9, x_128);
lean_ctor_set(x_135, 10, x_129);
lean_ctor_set(x_135, 11, x_130);
x_136 = lean_st_ref_set(x_2, x_135, x_118);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec_ref(x_136);
x_7 = x_137;
goto _start;
}
}
else
{
uint8_t x_139; 
lean_dec(x_53);
lean_free_object(x_21);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_55);
if (x_139 == 0)
{
return x_55;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_55, 0);
x_141 = lean_ctor_get(x_55, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_55);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_free_object(x_21);
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_52);
if (x_143 == 0)
{
return x_52;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_52, 0);
x_145 = lean_ctor_get(x_52, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_52);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
else
{
lean_dec(x_41);
lean_free_object(x_21);
lean_dec_ref(x_36);
goto block_50;
}
block_50:
{
uint8_t x_43; lean_object* x_44; 
x_43 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_44 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_34, x_35, x_43, x_1, x_2, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_mkFVar(x_18);
x_47 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_46, x_2, x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_7 = x_48;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_44;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_21, 2);
x_148 = lean_ctor_get(x_21, 3);
x_149 = lean_ctor_get(x_21, 4);
x_150 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_21);
x_151 = l_Lean_Meta_getZetaDeltaFVarIds___redArg(x_4, x_32);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
if (x_150 == 0)
{
uint8_t x_162; 
x_162 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(x_18, x_152);
lean_dec(x_152);
if (x_162 == 0)
{
lean_dec_ref(x_149);
goto block_161;
}
else
{
lean_object* x_163; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_163 = l_Lean_Meta_Closure_collectExpr(x_148, x_1, x_2, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_166 = l_Lean_Meta_Closure_collectExpr(x_149, x_1, x_2, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_st_ref_take(x_2, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_170, 2);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_170, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_170, 4);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_170, 5);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_170, 6);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_170, 7);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_170, 8);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 9);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_170, 10);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_170, 11);
lean_inc_ref(x_183);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 lean_ctor_release(x_170, 5);
 lean_ctor_release(x_170, 6);
 lean_ctor_release(x_170, 7);
 lean_ctor_release(x_170, 8);
 lean_ctor_release(x_170, 9);
 lean_ctor_release(x_170, 10);
 lean_ctor_release(x_170, 11);
 x_184 = x_170;
} else {
 lean_dec_ref(x_170);
 x_184 = lean_box(0);
}
x_185 = lean_unsigned_to_nat(0u);
x_186 = 0;
lean_inc(x_167);
lean_inc(x_19);
x_187 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_19);
lean_ctor_set(x_187, 2, x_147);
lean_ctor_set(x_187, 3, x_164);
lean_ctor_set(x_187, 4, x_167);
lean_ctor_set_uint8(x_187, sizeof(void*)*5, x_150);
lean_ctor_set_uint8(x_187, sizeof(void*)*5 + 1, x_186);
x_188 = lean_array_push(x_179, x_187);
if (lean_is_scalar(x_184)) {
 x_189 = lean_alloc_ctor(0, 12, 0);
} else {
 x_189 = x_184;
}
lean_ctor_set(x_189, 0, x_172);
lean_ctor_set(x_189, 1, x_173);
lean_ctor_set(x_189, 2, x_174);
lean_ctor_set(x_189, 3, x_175);
lean_ctor_set(x_189, 4, x_176);
lean_ctor_set(x_189, 5, x_177);
lean_ctor_set(x_189, 6, x_178);
lean_ctor_set(x_189, 7, x_188);
lean_ctor_set(x_189, 8, x_180);
lean_ctor_set(x_189, 9, x_181);
lean_ctor_set(x_189, 10, x_182);
lean_ctor_set(x_189, 11, x_183);
x_190 = lean_st_ref_set(x_2, x_189, x_171);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_st_ref_take(x_2, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_193, 2);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 4);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_193, 5);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_193, 6);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_193, 7);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_193, 8);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 9);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_193, 10);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_193, 11);
lean_inc_ref(x_206);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 lean_ctor_release(x_193, 6);
 lean_ctor_release(x_193, 7);
 lean_ctor_release(x_193, 8);
 lean_ctor_release(x_193, 9);
 lean_ctor_release(x_193, 10);
 lean_ctor_release(x_193, 11);
 x_207 = x_193;
} else {
 lean_dec_ref(x_193);
 x_207 = lean_box(0);
}
x_208 = lean_array_size(x_200);
x_209 = 0;
x_210 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_167, x_208, x_209, x_200);
lean_dec(x_167);
if (lean_is_scalar(x_207)) {
 x_211 = lean_alloc_ctor(0, 12, 0);
} else {
 x_211 = x_207;
}
lean_ctor_set(x_211, 0, x_195);
lean_ctor_set(x_211, 1, x_196);
lean_ctor_set(x_211, 2, x_197);
lean_ctor_set(x_211, 3, x_198);
lean_ctor_set(x_211, 4, x_199);
lean_ctor_set(x_211, 5, x_210);
lean_ctor_set(x_211, 6, x_201);
lean_ctor_set(x_211, 7, x_202);
lean_ctor_set(x_211, 8, x_203);
lean_ctor_set(x_211, 9, x_204);
lean_ctor_set(x_211, 10, x_205);
lean_ctor_set(x_211, 11, x_206);
x_212 = lean_st_ref_set(x_2, x_211, x_194);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec_ref(x_212);
x_7 = x_213;
goto _start;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_164);
lean_dec(x_147);
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_215 = lean_ctor_get(x_166, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_166, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_217 = x_166;
} else {
 lean_dec_ref(x_166);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_219 = lean_ctor_get(x_163, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_163, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_221 = x_163;
} else {
 lean_dec_ref(x_163);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
lean_dec(x_152);
lean_dec_ref(x_149);
goto block_161;
}
block_161:
{
uint8_t x_154; lean_object* x_155; 
x_154 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_155 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_147, x_148, x_154, x_1, x_2, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l_Lean_mkFVar(x_18);
x_158 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_157, x_2, x_156);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec_ref(x_158);
x_7 = x_159;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_155;
}
}
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_20);
if (x_223 == 0)
{
return x_20;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_20, 0);
x_225 = lean_ctor_get(x_20, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_20);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_Closure_process_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Meta_Closure_process(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_toExpr(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
lean_dec_ref(x_7);
x_11 = lean_expr_abstract_range(x_9, x_4, x_2);
lean_dec_ref(x_9);
if (x_3 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_mkForall(x_8, x_10, x_11, x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_mkLambda(x_8, x_10, x_11, x_6);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec_ref(x_7);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_expr_has_loose_bvar(x_6, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_expr_lower_loose_bvars(x_6, x_20, x_20);
lean_dec_ref(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_expr_abstract_range(x_15, x_4, x_2);
lean_dec_ref(x_15);
x_23 = lean_expr_abstract_range(x_16, x_4, x_2);
lean_dec_ref(x_16);
x_24 = l_Lean_Expr_letE___override(x_14, x_22, x_23, x_6, x_17);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Closure_mkBinding___closed__1;
x_2 = l_Lean_Meta_Closure_mkBinding___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_mkBinding___closed__5;
x_2 = l_Lean_Meta_Closure_mkBinding___closed__4;
x_3 = l_Lean_Meta_Closure_mkBinding___closed__3;
x_4 = l_Lean_Meta_Closure_mkBinding___closed__2;
x_5 = l_Lean_Meta_Closure_mkBinding___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkBinding___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Closure_mkBinding___closed__6;
x_2 = l_Lean_Meta_Closure_mkBinding___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0), 1, 0);
x_5 = l_Lean_Meta_Closure_mkBinding___closed__9;
x_6 = lean_array_size(x_2);
x_7 = 0;
lean_inc_ref(x_2);
x_8 = l_Array_mapMUnsafe_map___redArg(x_5, x_4, x_6, x_7, x_2);
x_9 = lean_box(x_1);
lean_inc(x_8);
lean_inc_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__1___boxed), 6, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_expr_abstract(x_3, x_8);
lean_dec(x_8);
x_12 = lean_array_get_size(x_2);
lean_dec_ref(x_2);
x_13 = l_Nat_foldRev___redArg(x_12, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lean_Meta_Closure_mkBinding___lam__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_LocalDecl_toExpr(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_7);
x_8 = lean_apply_3(x_1, x_7, lean_box(0), x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
lean_dec_ref(x_6);
x_10 = lean_expr_abstract_range(x_8, x_3, x_2);
lean_dec_ref(x_8);
x_11 = l_Lean_mkLambda(x_7, x_9, x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec_ref(x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_expr_has_loose_bvar(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_expr_lower_loose_bvars(x_5, x_18, x_18);
lean_dec_ref(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_expr_abstract_range(x_13, x_3, x_2);
lean_dec_ref(x_13);
x_21 = lean_expr_abstract_range(x_14, x_3, x_2);
lean_dec_ref(x_14);
x_22 = l_Lean_Expr_letE___override(x_12, x_20, x_21, x_5, x_15);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
x_10 = l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0(x_1, x_2, x_9, lean_box(0), x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = l_Nat_foldRev___at___Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1_spec__1(x_7, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_size(x_1);
x_4 = 0;
lean_inc_ref(x_1);
x_5 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_3, x_4, x_1);
x_6 = lean_expr_abstract(x_2, x_5);
x_7 = lean_array_get_size(x_1);
x_8 = l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1(x_1, x_5, x_7, x_6);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkLambda(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
lean_dec_ref(x_6);
x_10 = lean_expr_abstract_range(x_8, x_3, x_2);
lean_dec_ref(x_8);
x_11 = l_Lean_mkForall(x_7, x_9, x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec_ref(x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_expr_has_loose_bvar(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_expr_lower_loose_bvars(x_5, x_18, x_18);
lean_dec_ref(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_expr_abstract_range(x_13, x_3, x_2);
lean_dec_ref(x_13);
x_21 = lean_expr_abstract_range(x_14, x_3, x_2);
lean_dec_ref(x_14);
x_22 = l_Lean_Expr_letE___override(x_12, x_20, x_21, x_5, x_15);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
x_10 = l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0(x_1, x_2, x_9, lean_box(0), x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = l_Nat_foldRev___at___Nat_foldRev___at___Lean_Meta_Closure_mkLambda_spec__1_spec__1(x_7, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_size(x_1);
x_4 = 0;
lean_inc_ref(x_1);
x_5 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_3, x_4, x_1);
x_6 = lean_expr_abstract(x_2, x_5);
x_7 = lean_array_get_size(x_1);
x_8 = l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0(x_1, x_5, x_7, x_6);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at___Lean_Meta_Closure_mkForall_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkForall(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
lean_ctor_set(x_6, 2, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
lean_ctor_set(x_6, 1, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4;
x_2 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3;
x_3 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2;
x_4 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
x_18 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5;
lean_ctor_set(x_14, 1, x_18);
x_19 = lean_st_ref_set(x_6, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_st_ref_take(x_6, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_22, 2);
x_26 = l_Lean_instFVarIdSetEmptyCollection;
lean_ctor_set(x_22, 2, x_26);
x_27 = lean_st_ref_set(x_6, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_29);
lean_dec(x_11);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_40; lean_object* x_41; uint8_t x_46; lean_object* x_47; 
x_46 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*7, x_46);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_47 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_50 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
lean_inc(x_6);
x_53 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_53, 1);
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 0, x_48);
lean_inc_ref(x_53);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_25, x_57, x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_29, x_57, x_59);
lean_dec_ref(x_57);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_53);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_51);
lean_inc_ref(x_66);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_25, x_67, x_65);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_29, x_67, x_69);
lean_dec_ref(x_67);
lean_dec(x_6);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_51);
lean_dec(x_48);
x_74 = lean_ctor_get(x_53, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_dec_ref(x_53);
x_40 = x_74;
x_41 = x_75;
goto block_45;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_76 = lean_ctor_get(x_50, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_50, 1);
lean_inc(x_77);
lean_dec_ref(x_50);
x_40 = x_76;
x_41 = x_77;
goto block_45;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_47, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_47, 1);
lean_inc(x_79);
lean_dec_ref(x_47);
x_40 = x_78;
x_41 = x_79;
goto block_45;
}
block_39:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_29, x_33, x_32);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_31);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(0);
x_43 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_25, x_42, x_41);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_31 = x_40;
x_32 = x_44;
goto block_39;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_97; lean_object* x_98; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_80 = lean_ctor_get(x_5, 0);
x_81 = lean_ctor_get(x_5, 1);
x_82 = lean_ctor_get(x_5, 2);
x_83 = lean_ctor_get(x_5, 3);
x_84 = lean_ctor_get(x_5, 4);
x_85 = lean_ctor_get(x_5, 5);
x_86 = lean_ctor_get(x_5, 6);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_88 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_5);
x_103 = 1;
x_104 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_104, 0, x_80);
lean_ctor_set(x_104, 1, x_81);
lean_ctor_set(x_104, 2, x_82);
lean_ctor_set(x_104, 3, x_83);
lean_ctor_set(x_104, 4, x_84);
lean_ctor_set(x_104, 5, x_85);
lean_ctor_set(x_104, 6, x_86);
lean_ctor_set_uint8(x_104, sizeof(void*)*7, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 1, x_87);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 2, x_88);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_104);
lean_inc(x_4);
x_105 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_104, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_104);
lean_inc(x_4);
x_108 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_104, x_6, x_7, x_8, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
lean_inc(x_6);
x_111 = l_Lean_Meta_Closure_process(x_3, x_4, x_104, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_109);
lean_inc_ref(x_114);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_25, x_115, x_112);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_29, x_115, x_117);
lean_dec_ref(x_115);
lean_dec(x_6);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_109);
lean_dec(x_106);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
lean_dec_ref(x_111);
x_97 = x_122;
x_98 = x_123;
goto block_102;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_106);
lean_dec_ref(x_104);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_124 = lean_ctor_get(x_108, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_108, 1);
lean_inc(x_125);
lean_dec_ref(x_108);
x_97 = x_124;
x_98 = x_125;
goto block_102;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_104);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
lean_dec_ref(x_105);
x_97 = x_126;
x_98 = x_127;
goto block_102;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_box(0);
x_92 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_29, x_91, x_90);
lean_dec(x_6);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
block_102:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_box(0);
x_100 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_25, x_99, x_98);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_89 = x_97;
x_90 = x_101;
goto block_96;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_156; lean_object* x_157; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_128 = lean_ctor_get(x_22, 0);
x_129 = lean_ctor_get(x_22, 1);
x_130 = lean_ctor_get(x_22, 2);
x_131 = lean_ctor_get(x_22, 3);
x_132 = lean_ctor_get(x_22, 4);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_22);
x_133 = l_Lean_instFVarIdSetEmptyCollection;
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_129);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_131);
lean_ctor_set(x_134, 4, x_132);
x_135 = lean_st_ref_set(x_6, x_134, x_23);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_137);
lean_dec(x_11);
x_138 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_5, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_5, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_5, 5);
lean_inc(x_143);
x_144 = lean_ctor_get(x_5, 6);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_146 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_147 = x_5;
} else {
 lean_dec_ref(x_5);
 x_147 = lean_box(0);
}
x_162 = 1;
if (lean_is_scalar(x_147)) {
 x_163 = lean_alloc_ctor(0, 7, 3);
} else {
 x_163 = x_147;
}
lean_ctor_set(x_163, 0, x_138);
lean_ctor_set(x_163, 1, x_139);
lean_ctor_set(x_163, 2, x_140);
lean_ctor_set(x_163, 3, x_141);
lean_ctor_set(x_163, 4, x_142);
lean_ctor_set(x_163, 5, x_143);
lean_ctor_set(x_163, 6, x_144);
lean_ctor_set_uint8(x_163, sizeof(void*)*7, x_162);
lean_ctor_set_uint8(x_163, sizeof(void*)*7 + 1, x_145);
lean_ctor_set_uint8(x_163, sizeof(void*)*7 + 2, x_146);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_163);
lean_inc(x_4);
x_164 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_163, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_163);
lean_inc(x_4);
x_167 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_163, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
lean_inc(x_6);
x_170 = l_Lean_Meta_Closure_process(x_3, x_4, x_163, x_6, x_7, x_8, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_165);
lean_ctor_set(x_173, 1, x_168);
lean_inc_ref(x_173);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_130, x_174, x_171);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_137, x_174, x_176);
lean_dec_ref(x_174);
lean_dec(x_6);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_168);
lean_dec(x_165);
x_181 = lean_ctor_get(x_170, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_170, 1);
lean_inc(x_182);
lean_dec_ref(x_170);
x_156 = x_181;
x_157 = x_182;
goto block_161;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_165);
lean_dec_ref(x_163);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_183 = lean_ctor_get(x_167, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_167, 1);
lean_inc(x_184);
lean_dec_ref(x_167);
x_156 = x_183;
x_157 = x_184;
goto block_161;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_163);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
x_185 = lean_ctor_get(x_164, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_164, 1);
lean_inc(x_186);
lean_dec_ref(x_164);
x_156 = x_185;
x_157 = x_186;
goto block_161;
}
block_155:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_box(0);
x_151 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_137, x_150, x_149);
lean_dec(x_6);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
block_161:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_box(0);
x_159 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_130, x_158, x_157);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec_ref(x_159);
x_148 = x_156;
x_149 = x_160;
goto block_155;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_227; lean_object* x_228; uint8_t x_233; lean_object* x_234; lean_object* x_235; 
x_187 = lean_ctor_get(x_14, 0);
x_188 = lean_ctor_get(x_14, 2);
x_189 = lean_ctor_get(x_14, 3);
x_190 = lean_ctor_get(x_14, 4);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_14);
x_191 = l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5;
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_192, 2, x_188);
lean_ctor_set(x_192, 3, x_189);
lean_ctor_set(x_192, 4, x_190);
x_193 = lean_st_ref_set(x_6, x_192, x_15);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_st_ref_take(x_6, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_196, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 3);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_196, 4);
lean_inc_ref(x_202);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_203 = x_196;
} else {
 lean_dec_ref(x_196);
 x_203 = lean_box(0);
}
x_204 = l_Lean_instFVarIdSetEmptyCollection;
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 5, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_199);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_201);
lean_ctor_set(x_205, 4, x_202);
x_206 = lean_st_ref_set(x_6, x_205, x_197);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
x_208 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_208);
lean_dec(x_11);
x_209 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_5, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_5, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_5, 5);
lean_inc(x_214);
x_215 = lean_ctor_get(x_5, 6);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_217 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_218 = x_5;
} else {
 lean_dec_ref(x_5);
 x_218 = lean_box(0);
}
x_233 = 1;
if (lean_is_scalar(x_218)) {
 x_234 = lean_alloc_ctor(0, 7, 3);
} else {
 x_234 = x_218;
}
lean_ctor_set(x_234, 0, x_209);
lean_ctor_set(x_234, 1, x_210);
lean_ctor_set(x_234, 2, x_211);
lean_ctor_set(x_234, 3, x_212);
lean_ctor_set(x_234, 4, x_213);
lean_ctor_set(x_234, 5, x_214);
lean_ctor_set(x_234, 6, x_215);
lean_ctor_set_uint8(x_234, sizeof(void*)*7, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*7 + 1, x_216);
lean_ctor_set_uint8(x_234, sizeof(void*)*7 + 2, x_217);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_234);
lean_inc(x_4);
x_235 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_234, x_6, x_7, x_8, x_207);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_234);
lean_inc(x_4);
x_238 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_234, x_6, x_7, x_8, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
lean_inc(x_6);
x_241 = l_Lean_Meta_Closure_process(x_3, x_4, x_234, x_6, x_7, x_8, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_236);
lean_ctor_set(x_244, 1, x_239);
lean_inc_ref(x_244);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_200, x_245, x_242);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_208, x_245, x_247);
lean_dec_ref(x_245);
lean_dec(x_6);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_244);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_239);
lean_dec(x_236);
x_252 = lean_ctor_get(x_241, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_241, 1);
lean_inc(x_253);
lean_dec_ref(x_241);
x_227 = x_252;
x_228 = x_253;
goto block_232;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_236);
lean_dec_ref(x_234);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
lean_dec_ref(x_238);
x_227 = x_254;
x_228 = x_255;
goto block_232;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_234);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
x_256 = lean_ctor_get(x_235, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_235, 1);
lean_inc(x_257);
lean_dec_ref(x_235);
x_227 = x_256;
x_228 = x_257;
goto block_232;
}
block_226:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_box(0);
x_222 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_6, x_208, x_221, x_220);
lean_dec(x_6);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
 lean_ctor_set_tag(x_225, 1);
}
lean_ctor_set(x_225, 0, x_219);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
block_232:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_box(0);
x_230 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_200, x_229, x_228);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec_ref(x_230);
x_219 = x_227;
x_220 = x_231;
goto block_226;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__7;
x_3 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__6;
x_4 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__4;
x_5 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_2);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set(x_5, 9, x_2);
lean_ctor_set(x_5, 10, x_2);
lean_ctor_set(x_5, 11, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__8;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_18, 5);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_18, 6);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_18, 7);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_18, 9);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_18, 10);
lean_inc_ref(x_27);
lean_dec(x_18);
x_28 = l_Array_reverse___redArg(x_23);
x_29 = l_Array_append___redArg(x_28, x_24);
lean_dec_ref(x_24);
x_30 = l_Array_reverse___redArg(x_25);
lean_inc_ref(x_30);
x_31 = l_Lean_Meta_Closure_mkForall(x_30, x_19);
lean_dec(x_19);
lean_inc_ref(x_29);
x_32 = l_Lean_Meta_Closure_mkForall(x_29, x_31);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Closure_mkLambda(x_30, x_20);
lean_dec(x_20);
x_34 = l_Lean_Meta_Closure_mkLambda(x_29, x_33);
lean_dec_ref(x_33);
x_35 = l_Array_reverse___redArg(x_27);
x_36 = l_Array_append___redArg(x_35, x_26);
lean_dec_ref(x_26);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_22);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_16, 0, x_37);
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_ctor_get(x_38, 2);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_38, 4);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_38, 5);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_38, 6);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_38, 7);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_38, 9);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_38, 10);
lean_inc_ref(x_48);
lean_dec(x_38);
x_49 = l_Array_reverse___redArg(x_44);
x_50 = l_Array_append___redArg(x_49, x_45);
lean_dec_ref(x_45);
x_51 = l_Array_reverse___redArg(x_46);
lean_inc_ref(x_51);
x_52 = l_Lean_Meta_Closure_mkForall(x_51, x_40);
lean_dec(x_40);
lean_inc_ref(x_50);
x_53 = l_Lean_Meta_Closure_mkForall(x_50, x_52);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Closure_mkLambda(x_51, x_41);
lean_dec(x_41);
x_55 = l_Lean_Meta_Closure_mkLambda(x_50, x_54);
lean_dec_ref(x_54);
x_56 = l_Array_reverse___redArg(x_48);
x_57 = l_Array_append___redArg(x_56, x_47);
lean_dec_ref(x_47);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_42);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_43);
lean_ctor_set(x_58, 4, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_39);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
return x_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; lean_object* x_23; uint8_t x_24; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_23 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_23);
lean_dec(x_9);
lean_inc_ref(x_23);
x_24 = l_Lean_Environment_hasUnsafe(x_23, x_3);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Environment_hasUnsafe(x_23, x_4);
x_19 = x_25;
goto block_22;
}
else
{
lean_dec_ref(x_23);
x_19 = x_24;
goto block_22;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
block_22:
{
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
x_12 = x_20;
goto block_18;
}
else
{
uint8_t x_21; 
x_21 = 0;
x_12 = x_21;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_30; uint32_t x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_23);
lean_dec(x_12);
lean_inc_ref(x_21);
x_30 = l_Lean_getMaxHeight(x_18, x_21);
x_31 = 1;
x_32 = lean_uint32_add(x_30, x_31);
x_33 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_33, 0, x_32);
x_34 = lean_array_to_list(x_19);
lean_inc(x_1);
x_35 = l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_34, x_20, x_21, x_33, x_9, x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_38);
x_39 = l_Lean_addDecl(x_38, x_8, x_9, x_37);
if (lean_obj_tag(x_39) == 0)
{
if (x_5 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_24 = x_40;
goto block_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_compileDecl(x_38, x_5, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_24 = x_43;
goto block_29;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_17);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_38);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_array_to_list(x_22);
x_26 = l_Lean_mkConst(x_1, x_25);
x_27 = l_Lean_mkAppN(x_26, x_23);
lean_dec_ref(x_23);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_17;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_52; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_mkAuxDefinition(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = 1;
x_14 = l_Lean_Meta_mkAuxDefinition(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_mkAuxDefinitionFor(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_18);
lean_dec(x_12);
x_19 = lean_array_to_list(x_14);
x_20 = 0;
x_21 = l_Lean_Meta_mkAuxLemma(x_19, x_15, x_16, x_4, x_5, x_20, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_array_to_list(x_17);
x_25 = l_Lean_mkConst(x_23, x_24);
x_26 = l_Lean_mkAppN(x_25, x_18);
lean_dec_ref(x_18);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_array_to_list(x_17);
x_30 = l_Lean_mkConst(x_27, x_29);
x_31 = l_Lean_mkAppN(x_30, x_18);
lean_dec_ref(x_18);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_mkAuxTheorem(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0 = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__0);
l_Lean_Meta_Closure_instInhabitedToProcessElement = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement);
l_Lean_Meta_Closure_visitLevel___closed__0 = _init_l_Lean_Meta_Closure_visitLevel___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_visitLevel___closed__0);
l_Lean_Meta_Closure_visitLevel___closed__1 = _init_l_Lean_Meta_Closure_visitLevel___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_visitLevel___closed__1);
l_Lean_Meta_Closure_visitExpr___closed__0 = _init_l_Lean_Meta_Closure_visitExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_visitExpr___closed__0);
l_Lean_Meta_Closure_visitExpr___closed__1 = _init_l_Lean_Meta_Closure_visitExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_visitExpr___closed__1);
l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0 = _init_l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0);
l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1 = _init_l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1);
l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0 = _init_l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0);
l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1 = _init_l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1);
l_Lean_Meta_Closure_mkBinding___closed__0 = _init_l_Lean_Meta_Closure_mkBinding___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__0);
l_Lean_Meta_Closure_mkBinding___closed__1 = _init_l_Lean_Meta_Closure_mkBinding___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__1);
l_Lean_Meta_Closure_mkBinding___closed__2 = _init_l_Lean_Meta_Closure_mkBinding___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__2);
l_Lean_Meta_Closure_mkBinding___closed__3 = _init_l_Lean_Meta_Closure_mkBinding___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__3);
l_Lean_Meta_Closure_mkBinding___closed__4 = _init_l_Lean_Meta_Closure_mkBinding___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__4);
l_Lean_Meta_Closure_mkBinding___closed__5 = _init_l_Lean_Meta_Closure_mkBinding___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__5);
l_Lean_Meta_Closure_mkBinding___closed__6 = _init_l_Lean_Meta_Closure_mkBinding___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__6);
l_Lean_Meta_Closure_mkBinding___closed__7 = _init_l_Lean_Meta_Closure_mkBinding___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__7);
l_Lean_Meta_Closure_mkBinding___closed__8 = _init_l_Lean_Meta_Closure_mkBinding___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__8);
l_Lean_Meta_Closure_mkBinding___closed__9 = _init_l_Lean_Meta_Closure_mkBinding___closed__9();
lean_mark_persistent(l_Lean_Meta_Closure_mkBinding___closed__9);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4);
l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5 = _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__5);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__0 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__2 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__3 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__4 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__5 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__6 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__7 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__7);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__8 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
