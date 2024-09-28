// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Lean.MetavarContext Lean.Environment Lean.AddDecl Lean.Util.FoldConsts Lean.Meta.Basic Lean.Meta.Check
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedLevel___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheoremFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__8;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__12;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__13;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__6;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__6;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__14;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__18;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_LocalDecl_index(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelParams___default;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaDeltaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__17;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheoremFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__8;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__7;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__9;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedLevel___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__15;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedLevel___default___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__4;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_toProcess___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__11;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__19;
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__7;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1() {
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
x_1 = l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_nextLevelIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLetDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_nextExprIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_exprMVarArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_exprFVarArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_toProcess___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Closure_visitLevel___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_level_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_level_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_264; 
x_264 = l_Lean_Level_hasMVar(x_2);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = l_Lean_Level_hasParam(x_2);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_2);
lean_ctor_set(x_266, 1, x_9);
return x_266;
}
else
{
lean_object* x_267; 
x_267 = lean_box(0);
x_10 = x_267;
goto block_263;
}
}
else
{
lean_object* x_268; 
x_268 = lean_box(0);
x_10 = x_268;
goto block_263;
}
block_263:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_get_size(x_17);
x_19 = l_Lean_Level_hash(x_2);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_17, x_30);
lean_dec(x_17);
x_32 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_2, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_11);
x_33 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_34 = lean_apply_8(x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = lean_usize_sub(x_47, x_28);
x_49 = lean_usize_land(x_26, x_48);
x_50 = lean_array_uget(x_45, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_44, x_52);
lean_dec(x_44);
lean_inc(x_35);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_35);
lean_ctor_set(x_54, 2, x_50);
x_55 = lean_array_uset(x_45, x_49, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_55);
lean_ctor_set(x_39, 1, x_62);
lean_ctor_set(x_39, 0, x_53);
x_63 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_35);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_35);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_ctor_set(x_39, 1, x_55);
lean_ctor_set(x_39, 0, x_53);
x_68 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_35);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_box(0);
x_74 = lean_array_uset(x_45, x_49, x_73);
lean_inc(x_35);
x_75 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_2, x_35, x_50);
x_76 = lean_array_uset(x_74, x_49, x_75);
lean_ctor_set(x_39, 1, x_76);
x_77 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_35);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_35);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_39, 0);
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_84 = lean_array_get_size(x_83);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = lean_usize_sub(x_85, x_28);
x_87 = lean_usize_land(x_26, x_86);
x_88 = lean_array_uget(x_83, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_82, x_90);
lean_dec(x_82);
lean_inc(x_35);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_35);
lean_ctor_set(x_92, 2, x_88);
x_93 = lean_array_uset(x_83, x_87, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_mul(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_38, 0, x_101);
x_102 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_35);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_38, 0, x_106);
x_107 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
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
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_35);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_83, x_87, x_111);
lean_inc(x_35);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_2, x_35, x_88);
x_114 = lean_array_uset(x_112, x_87, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_82);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_38, 0, x_115);
x_116 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; size_t x_136; size_t x_137; lean_object* x_138; uint8_t x_139; 
x_120 = lean_ctor_get(x_38, 1);
x_121 = lean_ctor_get(x_38, 2);
x_122 = lean_ctor_get(x_38, 3);
x_123 = lean_ctor_get(x_38, 4);
x_124 = lean_ctor_get(x_38, 5);
x_125 = lean_ctor_get(x_38, 6);
x_126 = lean_ctor_get(x_38, 7);
x_127 = lean_ctor_get(x_38, 8);
x_128 = lean_ctor_get(x_38, 9);
x_129 = lean_ctor_get(x_38, 10);
x_130 = lean_ctor_get(x_38, 11);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_38);
x_131 = lean_ctor_get(x_39, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_39, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_133 = x_39;
} else {
 lean_dec_ref(x_39);
 x_133 = lean_box(0);
}
x_134 = lean_array_get_size(x_132);
x_135 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_136 = lean_usize_sub(x_135, x_28);
x_137 = lean_usize_land(x_26, x_136);
x_138 = lean_array_uget(x_132, x_137);
x_139 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_131, x_140);
lean_dec(x_131);
lean_inc(x_35);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_35);
lean_ctor_set(x_142, 2, x_138);
x_143 = lean_array_uset(x_132, x_137, x_142);
x_144 = lean_unsigned_to_nat(4u);
x_145 = lean_nat_mul(x_141, x_144);
x_146 = lean_unsigned_to_nat(3u);
x_147 = lean_nat_div(x_145, x_146);
lean_dec(x_145);
x_148 = lean_array_get_size(x_143);
x_149 = lean_nat_dec_le(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_143);
if (lean_is_scalar(x_133)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_133;
}
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_120);
lean_ctor_set(x_152, 2, x_121);
lean_ctor_set(x_152, 3, x_122);
lean_ctor_set(x_152, 4, x_123);
lean_ctor_set(x_152, 5, x_124);
lean_ctor_set(x_152, 6, x_125);
lean_ctor_set(x_152, 7, x_126);
lean_ctor_set(x_152, 8, x_127);
lean_ctor_set(x_152, 9, x_128);
lean_ctor_set(x_152, 10, x_129);
lean_ctor_set(x_152, 11, x_130);
x_153 = lean_st_ref_set(x_4, x_152, x_40);
lean_dec(x_4);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_35);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_scalar(x_133)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_133;
}
lean_ctor_set(x_157, 0, x_141);
lean_ctor_set(x_157, 1, x_143);
x_158 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_120);
lean_ctor_set(x_158, 2, x_121);
lean_ctor_set(x_158, 3, x_122);
lean_ctor_set(x_158, 4, x_123);
lean_ctor_set(x_158, 5, x_124);
lean_ctor_set(x_158, 6, x_125);
lean_ctor_set(x_158, 7, x_126);
lean_ctor_set(x_158, 8, x_127);
lean_ctor_set(x_158, 9, x_128);
lean_ctor_set(x_158, 10, x_129);
lean_ctor_set(x_158, 11, x_130);
x_159 = lean_st_ref_set(x_4, x_158, x_40);
lean_dec(x_4);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_box(0);
x_164 = lean_array_uset(x_132, x_137, x_163);
lean_inc(x_35);
x_165 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_2, x_35, x_138);
x_166 = lean_array_uset(x_164, x_137, x_165);
if (lean_is_scalar(x_133)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_133;
}
lean_ctor_set(x_167, 0, x_131);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_120);
lean_ctor_set(x_168, 2, x_121);
lean_ctor_set(x_168, 3, x_122);
lean_ctor_set(x_168, 4, x_123);
lean_ctor_set(x_168, 5, x_124);
lean_ctor_set(x_168, 6, x_125);
lean_ctor_set(x_168, 7, x_126);
lean_ctor_set(x_168, 8, x_127);
lean_ctor_set(x_168, 9, x_128);
lean_ctor_set(x_168, 10, x_129);
lean_ctor_set(x_168, 11, x_130);
x_169 = lean_st_ref_set(x_4, x_168, x_40);
lean_dec(x_4);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_35);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_4);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_34);
if (x_173 == 0)
{
return x_34;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_34, 0);
x_175 = lean_ctor_get(x_34, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_34);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_32, 0);
lean_inc(x_177);
lean_dec(x_32);
lean_ctor_set(x_11, 0, x_177);
return x_11;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; 
x_178 = lean_ctor_get(x_11, 1);
lean_inc(x_178);
lean_dec(x_11);
x_179 = lean_ctor_get(x_13, 1);
lean_inc(x_179);
lean_dec(x_13);
x_180 = lean_array_get_size(x_179);
x_181 = l_Lean_Level_hash(x_2);
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
lean_dec(x_179);
x_194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_2, x_193);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_196 = lean_apply_8(x_1, x_2, x_195, x_4, x_5, x_6, x_7, x_8, x_178);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; size_t x_221; lean_object* x_222; uint8_t x_223; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_st_ref_take(x_4, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 6);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 7);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 8);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 9);
lean_inc(x_211);
x_212 = lean_ctor_get(x_200, 10);
lean_inc(x_212);
x_213 = lean_ctor_get(x_200, 11);
lean_inc(x_213);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 lean_ctor_release(x_200, 6);
 lean_ctor_release(x_200, 7);
 lean_ctor_release(x_200, 8);
 lean_ctor_release(x_200, 9);
 lean_ctor_release(x_200, 10);
 lean_ctor_release(x_200, 11);
 x_214 = x_200;
} else {
 lean_dec_ref(x_200);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_201, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_201, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_217 = x_201;
} else {
 lean_dec_ref(x_201);
 x_217 = lean_box(0);
}
x_218 = lean_array_get_size(x_216);
x_219 = lean_usize_of_nat(x_218);
lean_dec(x_218);
x_220 = lean_usize_sub(x_219, x_190);
x_221 = lean_usize_land(x_188, x_220);
x_222 = lean_array_uget(x_216, x_221);
x_223 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_215, x_224);
lean_dec(x_215);
lean_inc(x_197);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_2);
lean_ctor_set(x_226, 1, x_197);
lean_ctor_set(x_226, 2, x_222);
x_227 = lean_array_uset(x_216, x_221, x_226);
x_228 = lean_unsigned_to_nat(4u);
x_229 = lean_nat_mul(x_225, x_228);
x_230 = lean_unsigned_to_nat(3u);
x_231 = lean_nat_div(x_229, x_230);
lean_dec(x_229);
x_232 = lean_array_get_size(x_227);
x_233 = lean_nat_dec_le(x_231, x_232);
lean_dec(x_232);
lean_dec(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_234 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_227);
if (lean_is_scalar(x_217)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_217;
}
lean_ctor_set(x_235, 0, x_225);
lean_ctor_set(x_235, 1, x_234);
if (lean_is_scalar(x_214)) {
 x_236 = lean_alloc_ctor(0, 12, 0);
} else {
 x_236 = x_214;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_203);
lean_ctor_set(x_236, 2, x_204);
lean_ctor_set(x_236, 3, x_205);
lean_ctor_set(x_236, 4, x_206);
lean_ctor_set(x_236, 5, x_207);
lean_ctor_set(x_236, 6, x_208);
lean_ctor_set(x_236, 7, x_209);
lean_ctor_set(x_236, 8, x_210);
lean_ctor_set(x_236, 9, x_211);
lean_ctor_set(x_236, 10, x_212);
lean_ctor_set(x_236, 11, x_213);
x_237 = lean_st_ref_set(x_4, x_236, x_202);
lean_dec(x_4);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_197);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
if (lean_is_scalar(x_217)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_217;
}
lean_ctor_set(x_241, 0, x_225);
lean_ctor_set(x_241, 1, x_227);
if (lean_is_scalar(x_214)) {
 x_242 = lean_alloc_ctor(0, 12, 0);
} else {
 x_242 = x_214;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_203);
lean_ctor_set(x_242, 2, x_204);
lean_ctor_set(x_242, 3, x_205);
lean_ctor_set(x_242, 4, x_206);
lean_ctor_set(x_242, 5, x_207);
lean_ctor_set(x_242, 6, x_208);
lean_ctor_set(x_242, 7, x_209);
lean_ctor_set(x_242, 8, x_210);
lean_ctor_set(x_242, 9, x_211);
lean_ctor_set(x_242, 10, x_212);
lean_ctor_set(x_242, 11, x_213);
x_243 = lean_st_ref_set(x_4, x_242, x_202);
lean_dec(x_4);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_197);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_247 = lean_box(0);
x_248 = lean_array_uset(x_216, x_221, x_247);
lean_inc(x_197);
x_249 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_2, x_197, x_222);
x_250 = lean_array_uset(x_248, x_221, x_249);
if (lean_is_scalar(x_217)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_217;
}
lean_ctor_set(x_251, 0, x_215);
lean_ctor_set(x_251, 1, x_250);
if (lean_is_scalar(x_214)) {
 x_252 = lean_alloc_ctor(0, 12, 0);
} else {
 x_252 = x_214;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_203);
lean_ctor_set(x_252, 2, x_204);
lean_ctor_set(x_252, 3, x_205);
lean_ctor_set(x_252, 4, x_206);
lean_ctor_set(x_252, 5, x_207);
lean_ctor_set(x_252, 6, x_208);
lean_ctor_set(x_252, 7, x_209);
lean_ctor_set(x_252, 8, x_210);
lean_ctor_set(x_252, 9, x_211);
lean_ctor_set(x_252, 10, x_212);
lean_ctor_set(x_252, 11, x_213);
x_253 = lean_st_ref_set(x_4, x_252, x_202);
lean_dec(x_4);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_197);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_4);
lean_dec(x_2);
x_257 = lean_ctor_get(x_196, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_196, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_259 = x_196;
} else {
 lean_dec_ref(x_196);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_194, 0);
lean_inc(x_261);
lean_dec(x_194);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_178);
return x_262;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitLevel(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_264; 
x_264 = l_Lean_Expr_hasLevelParam(x_2);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = l_Lean_Expr_hasFVar(x_2);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = l_Lean_Expr_hasMVar(x_2);
if (x_266 == 0)
{
lean_object* x_267; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_2);
lean_ctor_set(x_267, 1, x_9);
return x_267;
}
else
{
lean_object* x_268; 
x_268 = lean_box(0);
x_10 = x_268;
goto block_263;
}
}
else
{
lean_object* x_269; 
x_269 = lean_box(0);
x_10 = x_269;
goto block_263;
}
}
else
{
lean_object* x_270; 
x_270 = lean_box(0);
x_10 = x_270;
goto block_263;
}
block_263:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_get_size(x_17);
x_19 = l_Lean_Expr_hash(x_2);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_17, x_30);
lean_dec(x_17);
x_32 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_2, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_11);
x_33 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_34 = lean_apply_8(x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = lean_usize_sub(x_47, x_28);
x_49 = lean_usize_land(x_26, x_48);
x_50 = lean_array_uget(x_45, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_2, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_44, x_52);
lean_dec(x_44);
lean_inc(x_35);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_35);
lean_ctor_set(x_54, 2, x_50);
x_55 = lean_array_uset(x_45, x_49, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_55);
lean_ctor_set(x_39, 1, x_62);
lean_ctor_set(x_39, 0, x_53);
x_63 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_35);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_35);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_ctor_set(x_39, 1, x_55);
lean_ctor_set(x_39, 0, x_53);
x_68 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_35);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_box(0);
x_74 = lean_array_uset(x_45, x_49, x_73);
lean_inc(x_35);
x_75 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_2, x_35, x_50);
x_76 = lean_array_uset(x_74, x_49, x_75);
lean_ctor_set(x_39, 1, x_76);
x_77 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_35);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_35);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_39, 0);
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_84 = lean_array_get_size(x_83);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = lean_usize_sub(x_85, x_28);
x_87 = lean_usize_land(x_26, x_86);
x_88 = lean_array_uget(x_83, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_2, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_82, x_90);
lean_dec(x_82);
lean_inc(x_35);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_35);
lean_ctor_set(x_92, 2, x_88);
x_93 = lean_array_uset(x_83, x_87, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_mul(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_38, 1, x_101);
x_102 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_35);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_38, 1, x_106);
x_107 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
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
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_35);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_83, x_87, x_111);
lean_inc(x_35);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_2, x_35, x_88);
x_114 = lean_array_uset(x_112, x_87, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_82);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_38, 1, x_115);
x_116 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; size_t x_136; size_t x_137; lean_object* x_138; uint8_t x_139; 
x_120 = lean_ctor_get(x_38, 0);
x_121 = lean_ctor_get(x_38, 2);
x_122 = lean_ctor_get(x_38, 3);
x_123 = lean_ctor_get(x_38, 4);
x_124 = lean_ctor_get(x_38, 5);
x_125 = lean_ctor_get(x_38, 6);
x_126 = lean_ctor_get(x_38, 7);
x_127 = lean_ctor_get(x_38, 8);
x_128 = lean_ctor_get(x_38, 9);
x_129 = lean_ctor_get(x_38, 10);
x_130 = lean_ctor_get(x_38, 11);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_38);
x_131 = lean_ctor_get(x_39, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_39, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_133 = x_39;
} else {
 lean_dec_ref(x_39);
 x_133 = lean_box(0);
}
x_134 = lean_array_get_size(x_132);
x_135 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_136 = lean_usize_sub(x_135, x_28);
x_137 = lean_usize_land(x_26, x_136);
x_138 = lean_array_uget(x_132, x_137);
x_139 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_2, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_131, x_140);
lean_dec(x_131);
lean_inc(x_35);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_35);
lean_ctor_set(x_142, 2, x_138);
x_143 = lean_array_uset(x_132, x_137, x_142);
x_144 = lean_unsigned_to_nat(4u);
x_145 = lean_nat_mul(x_141, x_144);
x_146 = lean_unsigned_to_nat(3u);
x_147 = lean_nat_div(x_145, x_146);
lean_dec(x_145);
x_148 = lean_array_get_size(x_143);
x_149 = lean_nat_dec_le(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_143);
if (lean_is_scalar(x_133)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_133;
}
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_152, 0, x_120);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_121);
lean_ctor_set(x_152, 3, x_122);
lean_ctor_set(x_152, 4, x_123);
lean_ctor_set(x_152, 5, x_124);
lean_ctor_set(x_152, 6, x_125);
lean_ctor_set(x_152, 7, x_126);
lean_ctor_set(x_152, 8, x_127);
lean_ctor_set(x_152, 9, x_128);
lean_ctor_set(x_152, 10, x_129);
lean_ctor_set(x_152, 11, x_130);
x_153 = lean_st_ref_set(x_4, x_152, x_40);
lean_dec(x_4);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_35);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_scalar(x_133)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_133;
}
lean_ctor_set(x_157, 0, x_141);
lean_ctor_set(x_157, 1, x_143);
x_158 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_158, 0, x_120);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_121);
lean_ctor_set(x_158, 3, x_122);
lean_ctor_set(x_158, 4, x_123);
lean_ctor_set(x_158, 5, x_124);
lean_ctor_set(x_158, 6, x_125);
lean_ctor_set(x_158, 7, x_126);
lean_ctor_set(x_158, 8, x_127);
lean_ctor_set(x_158, 9, x_128);
lean_ctor_set(x_158, 10, x_129);
lean_ctor_set(x_158, 11, x_130);
x_159 = lean_st_ref_set(x_4, x_158, x_40);
lean_dec(x_4);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_box(0);
x_164 = lean_array_uset(x_132, x_137, x_163);
lean_inc(x_35);
x_165 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_2, x_35, x_138);
x_166 = lean_array_uset(x_164, x_137, x_165);
if (lean_is_scalar(x_133)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_133;
}
lean_ctor_set(x_167, 0, x_131);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_168, 0, x_120);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_121);
lean_ctor_set(x_168, 3, x_122);
lean_ctor_set(x_168, 4, x_123);
lean_ctor_set(x_168, 5, x_124);
lean_ctor_set(x_168, 6, x_125);
lean_ctor_set(x_168, 7, x_126);
lean_ctor_set(x_168, 8, x_127);
lean_ctor_set(x_168, 9, x_128);
lean_ctor_set(x_168, 10, x_129);
lean_ctor_set(x_168, 11, x_130);
x_169 = lean_st_ref_set(x_4, x_168, x_40);
lean_dec(x_4);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_35);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_4);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_34);
if (x_173 == 0)
{
return x_34;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_34, 0);
x_175 = lean_ctor_get(x_34, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_34);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_32, 0);
lean_inc(x_177);
lean_dec(x_32);
lean_ctor_set(x_11, 0, x_177);
return x_11;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; 
x_178 = lean_ctor_get(x_11, 1);
lean_inc(x_178);
lean_dec(x_11);
x_179 = lean_ctor_get(x_13, 1);
lean_inc(x_179);
lean_dec(x_13);
x_180 = lean_array_get_size(x_179);
x_181 = l_Lean_Expr_hash(x_2);
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
lean_dec(x_179);
x_194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_2, x_193);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_196 = lean_apply_8(x_1, x_2, x_195, x_4, x_5, x_6, x_7, x_8, x_178);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; size_t x_221; lean_object* x_222; uint8_t x_223; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_st_ref_take(x_4, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 6);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 7);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 8);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 9);
lean_inc(x_211);
x_212 = lean_ctor_get(x_200, 10);
lean_inc(x_212);
x_213 = lean_ctor_get(x_200, 11);
lean_inc(x_213);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 lean_ctor_release(x_200, 6);
 lean_ctor_release(x_200, 7);
 lean_ctor_release(x_200, 8);
 lean_ctor_release(x_200, 9);
 lean_ctor_release(x_200, 10);
 lean_ctor_release(x_200, 11);
 x_214 = x_200;
} else {
 lean_dec_ref(x_200);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_201, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_201, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_217 = x_201;
} else {
 lean_dec_ref(x_201);
 x_217 = lean_box(0);
}
x_218 = lean_array_get_size(x_216);
x_219 = lean_usize_of_nat(x_218);
lean_dec(x_218);
x_220 = lean_usize_sub(x_219, x_190);
x_221 = lean_usize_land(x_188, x_220);
x_222 = lean_array_uget(x_216, x_221);
x_223 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_2, x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_215, x_224);
lean_dec(x_215);
lean_inc(x_197);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_2);
lean_ctor_set(x_226, 1, x_197);
lean_ctor_set(x_226, 2, x_222);
x_227 = lean_array_uset(x_216, x_221, x_226);
x_228 = lean_unsigned_to_nat(4u);
x_229 = lean_nat_mul(x_225, x_228);
x_230 = lean_unsigned_to_nat(3u);
x_231 = lean_nat_div(x_229, x_230);
lean_dec(x_229);
x_232 = lean_array_get_size(x_227);
x_233 = lean_nat_dec_le(x_231, x_232);
lean_dec(x_232);
lean_dec(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_234 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_227);
if (lean_is_scalar(x_217)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_217;
}
lean_ctor_set(x_235, 0, x_225);
lean_ctor_set(x_235, 1, x_234);
if (lean_is_scalar(x_214)) {
 x_236 = lean_alloc_ctor(0, 12, 0);
} else {
 x_236 = x_214;
}
lean_ctor_set(x_236, 0, x_203);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_236, 2, x_204);
lean_ctor_set(x_236, 3, x_205);
lean_ctor_set(x_236, 4, x_206);
lean_ctor_set(x_236, 5, x_207);
lean_ctor_set(x_236, 6, x_208);
lean_ctor_set(x_236, 7, x_209);
lean_ctor_set(x_236, 8, x_210);
lean_ctor_set(x_236, 9, x_211);
lean_ctor_set(x_236, 10, x_212);
lean_ctor_set(x_236, 11, x_213);
x_237 = lean_st_ref_set(x_4, x_236, x_202);
lean_dec(x_4);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_197);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
if (lean_is_scalar(x_217)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_217;
}
lean_ctor_set(x_241, 0, x_225);
lean_ctor_set(x_241, 1, x_227);
if (lean_is_scalar(x_214)) {
 x_242 = lean_alloc_ctor(0, 12, 0);
} else {
 x_242 = x_214;
}
lean_ctor_set(x_242, 0, x_203);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set(x_242, 2, x_204);
lean_ctor_set(x_242, 3, x_205);
lean_ctor_set(x_242, 4, x_206);
lean_ctor_set(x_242, 5, x_207);
lean_ctor_set(x_242, 6, x_208);
lean_ctor_set(x_242, 7, x_209);
lean_ctor_set(x_242, 8, x_210);
lean_ctor_set(x_242, 9, x_211);
lean_ctor_set(x_242, 10, x_212);
lean_ctor_set(x_242, 11, x_213);
x_243 = lean_st_ref_set(x_4, x_242, x_202);
lean_dec(x_4);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_197);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_247 = lean_box(0);
x_248 = lean_array_uset(x_216, x_221, x_247);
lean_inc(x_197);
x_249 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_2, x_197, x_222);
x_250 = lean_array_uset(x_248, x_221, x_249);
if (lean_is_scalar(x_217)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_217;
}
lean_ctor_set(x_251, 0, x_215);
lean_ctor_set(x_251, 1, x_250);
if (lean_is_scalar(x_214)) {
 x_252 = lean_alloc_ctor(0, 12, 0);
} else {
 x_252 = x_214;
}
lean_ctor_set(x_252, 0, x_203);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_204);
lean_ctor_set(x_252, 3, x_205);
lean_ctor_set(x_252, 4, x_206);
lean_ctor_set(x_252, 5, x_207);
lean_ctor_set(x_252, 6, x_208);
lean_ctor_set(x_252, 7, x_209);
lean_ctor_set(x_252, 8, x_210);
lean_ctor_set(x_252, 9, x_211);
lean_ctor_set(x_252, 10, x_212);
lean_ctor_set(x_252, 11, x_213);
x_253 = lean_st_ref_set(x_4, x_252, x_202);
lean_dec(x_4);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_197);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_4);
lean_dec(x_2);
x_257 = lean_ctor_get(x_196, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_196, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_259 = x_196;
} else {
 lean_dec_ref(x_196);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_194, 0);
lean_inc(x_261);
lean_dec(x_194);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_178);
return x_262;
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
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitExpr(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("u", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
x_14 = lean_name_append_index_after(x_13, x_12);
x_15 = lean_st_ref_take(x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_14);
x_22 = lean_array_push(x_19, x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_20, x_23);
lean_dec(x_20);
x_25 = lean_array_push(x_21, x_1);
lean_ctor_set(x_16, 4, x_25);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_22);
x_26 = lean_st_ref_set(x_3, x_16, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Level_param___override(x_14);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Level_param___override(x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
x_35 = lean_ctor_get(x_16, 2);
x_36 = lean_ctor_get(x_16, 3);
x_37 = lean_ctor_get(x_16, 4);
x_38 = lean_ctor_get(x_16, 5);
x_39 = lean_ctor_get(x_16, 6);
x_40 = lean_ctor_get(x_16, 7);
x_41 = lean_ctor_get(x_16, 8);
x_42 = lean_ctor_get(x_16, 9);
x_43 = lean_ctor_get(x_16, 10);
x_44 = lean_ctor_get(x_16, 11);
lean_inc(x_44);
lean_inc(x_43);
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
lean_dec(x_16);
lean_inc(x_14);
x_45 = lean_array_push(x_35, x_14);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_36, x_46);
lean_dec(x_36);
x_48 = lean_array_push(x_37, x_1);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_38);
lean_ctor_set(x_49, 6, x_39);
lean_ctor_set(x_49, 7, x_40);
lean_ctor_set(x_49, 8, x_41);
lean_ctor_set(x_49, 9, x_42);
lean_ctor_set(x_49, 10, x_43);
lean_ctor_set(x_49, 11, x_44);
x_50 = lean_st_ref_set(x_3, x_49, x_17);
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
x_53 = l_Lean_Level_param___override(x_14);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateSucc!Impl", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ level expected", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__2;
x_3 = lean_unsigned_to_nat(541u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateMax!Impl", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max level expected", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__5;
x_3 = lean_unsigned_to_nat(552u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateIMax!Impl", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imax level expected", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__8;
x_3 = lean_unsigned_to_nat(563u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; uint8_t x_133; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_133 = l_Lean_Level_hasMVar(x_23);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Level_hasParam(x_23);
if (x_134 == 0)
{
x_9 = x_23;
x_10 = x_8;
goto block_21;
}
else
{
lean_object* x_135; 
x_135 = lean_box(0);
x_24 = x_135;
goto block_132;
}
}
else
{
lean_object* x_136; 
x_136 = lean_box(0);
x_24 = x_136;
goto block_132;
}
block_132:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
x_25 = lean_st_ref_get(x_3, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_29);
x_31 = l_Lean_Level_hash(x_23);
x_32 = 32;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = 16;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = 1;
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_29, x_42);
lean_dec(x_29);
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_23, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_inc(x_23);
x_45 = l_Lean_Meta_Closure_collectLevelAux(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_take(x_3, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 7);
lean_inc(x_58);
x_59 = lean_ctor_get(x_49, 8);
lean_inc(x_59);
x_60 = lean_ctor_get(x_49, 9);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 10);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 11);
lean_inc(x_62);
lean_dec(x_49);
x_63 = !lean_is_exclusive(x_50);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_50, 0);
x_65 = lean_ctor_get(x_50, 1);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = lean_usize_sub(x_67, x_40);
x_69 = lean_usize_land(x_38, x_68);
x_70 = lean_array_uget(x_65, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_23, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_64, x_72);
lean_dec(x_64);
lean_inc(x_46);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_23);
lean_ctor_set(x_74, 1, x_46);
lean_ctor_set(x_74, 2, x_70);
x_75 = lean_array_uset(x_65, x_69, x_74);
x_76 = lean_unsigned_to_nat(4u);
x_77 = lean_nat_mul(x_73, x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_div(x_77, x_78);
lean_dec(x_77);
x_80 = lean_array_get_size(x_75);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_75);
lean_ctor_set(x_50, 1, x_82);
lean_ctor_set(x_50, 0, x_73);
x_83 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_52);
lean_ctor_set(x_83, 2, x_53);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set(x_83, 4, x_55);
lean_ctor_set(x_83, 5, x_56);
lean_ctor_set(x_83, 6, x_57);
lean_ctor_set(x_83, 7, x_58);
lean_ctor_set(x_83, 8, x_59);
lean_ctor_set(x_83, 9, x_60);
lean_ctor_set(x_83, 10, x_61);
lean_ctor_set(x_83, 11, x_62);
x_84 = lean_st_ref_set(x_3, x_83, x_51);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_9 = x_46;
x_10 = x_85;
goto block_21;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_ctor_set(x_50, 1, x_75);
lean_ctor_set(x_50, 0, x_73);
x_86 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_86, 0, x_50);
lean_ctor_set(x_86, 1, x_52);
lean_ctor_set(x_86, 2, x_53);
lean_ctor_set(x_86, 3, x_54);
lean_ctor_set(x_86, 4, x_55);
lean_ctor_set(x_86, 5, x_56);
lean_ctor_set(x_86, 6, x_57);
lean_ctor_set(x_86, 7, x_58);
lean_ctor_set(x_86, 8, x_59);
lean_ctor_set(x_86, 9, x_60);
lean_ctor_set(x_86, 10, x_61);
lean_ctor_set(x_86, 11, x_62);
x_87 = lean_st_ref_set(x_3, x_86, x_51);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_9 = x_46;
x_10 = x_88;
goto block_21;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_box(0);
x_90 = lean_array_uset(x_65, x_69, x_89);
lean_inc(x_46);
x_91 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_23, x_46, x_70);
x_92 = lean_array_uset(x_90, x_69, x_91);
lean_ctor_set(x_50, 1, x_92);
x_93 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_93, 0, x_50);
lean_ctor_set(x_93, 1, x_52);
lean_ctor_set(x_93, 2, x_53);
lean_ctor_set(x_93, 3, x_54);
lean_ctor_set(x_93, 4, x_55);
lean_ctor_set(x_93, 5, x_56);
lean_ctor_set(x_93, 6, x_57);
lean_ctor_set(x_93, 7, x_58);
lean_ctor_set(x_93, 8, x_59);
lean_ctor_set(x_93, 9, x_60);
lean_ctor_set(x_93, 10, x_61);
lean_ctor_set(x_93, 11, x_62);
x_94 = lean_st_ref_set(x_3, x_93, x_51);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_9 = x_46;
x_10 = x_95;
goto block_21;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; uint8_t x_103; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_50);
x_98 = lean_array_get_size(x_97);
x_99 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_100 = lean_usize_sub(x_99, x_40);
x_101 = lean_usize_land(x_38, x_100);
x_102 = lean_array_uget(x_97, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_23, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_96, x_104);
lean_dec(x_96);
lean_inc(x_46);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_23);
lean_ctor_set(x_106, 1, x_46);
lean_ctor_set(x_106, 2, x_102);
x_107 = lean_array_uset(x_97, x_101, x_106);
x_108 = lean_unsigned_to_nat(4u);
x_109 = lean_nat_mul(x_105, x_108);
x_110 = lean_unsigned_to_nat(3u);
x_111 = lean_nat_div(x_109, x_110);
lean_dec(x_109);
x_112 = lean_array_get_size(x_107);
x_113 = lean_nat_dec_le(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_52);
lean_ctor_set(x_116, 2, x_53);
lean_ctor_set(x_116, 3, x_54);
lean_ctor_set(x_116, 4, x_55);
lean_ctor_set(x_116, 5, x_56);
lean_ctor_set(x_116, 6, x_57);
lean_ctor_set(x_116, 7, x_58);
lean_ctor_set(x_116, 8, x_59);
lean_ctor_set(x_116, 9, x_60);
lean_ctor_set(x_116, 10, x_61);
lean_ctor_set(x_116, 11, x_62);
x_117 = lean_st_ref_set(x_3, x_116, x_51);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_9 = x_46;
x_10 = x_118;
goto block_21;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_105);
lean_ctor_set(x_119, 1, x_107);
x_120 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_52);
lean_ctor_set(x_120, 2, x_53);
lean_ctor_set(x_120, 3, x_54);
lean_ctor_set(x_120, 4, x_55);
lean_ctor_set(x_120, 5, x_56);
lean_ctor_set(x_120, 6, x_57);
lean_ctor_set(x_120, 7, x_58);
lean_ctor_set(x_120, 8, x_59);
lean_ctor_set(x_120, 9, x_60);
lean_ctor_set(x_120, 10, x_61);
lean_ctor_set(x_120, 11, x_62);
x_121 = lean_st_ref_set(x_3, x_120, x_51);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_9 = x_46;
x_10 = x_122;
goto block_21;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_box(0);
x_124 = lean_array_uset(x_97, x_101, x_123);
lean_inc(x_46);
x_125 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_23, x_46, x_102);
x_126 = lean_array_uset(x_124, x_101, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_96);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_52);
lean_ctor_set(x_128, 2, x_53);
lean_ctor_set(x_128, 3, x_54);
lean_ctor_set(x_128, 4, x_55);
lean_ctor_set(x_128, 5, x_56);
lean_ctor_set(x_128, 6, x_57);
lean_ctor_set(x_128, 7, x_58);
lean_ctor_set(x_128, 8, x_59);
lean_ctor_set(x_128, 9, x_60);
lean_ctor_set(x_128, 10, x_61);
lean_ctor_set(x_128, 11, x_62);
x_129 = lean_st_ref_set(x_3, x_128, x_51);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_9 = x_46;
x_10 = x_130;
goto block_21;
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_23);
x_131 = lean_ctor_get(x_44, 0);
lean_inc(x_131);
lean_dec(x_44);
x_9 = x_131;
x_10 = x_28;
goto block_21;
}
}
}
case 2:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_275; uint8_t x_384; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc(x_138);
x_384 = l_Lean_Level_hasMVar(x_137);
if (x_384 == 0)
{
uint8_t x_385; 
x_385 = l_Lean_Level_hasParam(x_137);
if (x_385 == 0)
{
x_139 = x_137;
x_140 = x_8;
goto block_274;
}
else
{
lean_object* x_386; 
x_386 = lean_box(0);
x_275 = x_386;
goto block_383;
}
}
else
{
lean_object* x_387; 
x_387 = lean_box(0);
x_275 = x_387;
goto block_383;
}
block_274:
{
lean_object* x_141; lean_object* x_142; lean_object* x_161; uint8_t x_270; 
x_270 = l_Lean_Level_hasMVar(x_138);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = l_Lean_Level_hasParam(x_138);
if (x_271 == 0)
{
x_141 = x_138;
x_142 = x_140;
goto block_160;
}
else
{
lean_object* x_272; 
x_272 = lean_box(0);
x_161 = x_272;
goto block_269;
}
}
else
{
lean_object* x_273; 
x_273 = lean_box(0);
x_161 = x_273;
goto block_269;
}
block_160:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_inc(x_144);
x_145 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_146 = lean_ptr_addr(x_139);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_1);
x_148 = l_Lean_mkLevelMax_x27(x_139, x_141);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_142);
return x_149;
}
else
{
size_t x_150; size_t x_151; uint8_t x_152; 
x_150 = lean_ptr_addr(x_144);
lean_dec(x_144);
x_151 = lean_ptr_addr(x_141);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_1);
x_153 = l_Lean_mkLevelMax_x27(x_139, x_141);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_142);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Lean_simpLevelMax_x27(x_139, x_141, x_1);
lean_dec(x_1);
lean_dec(x_141);
lean_dec(x_139);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_142);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_1);
x_157 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_158 = l_panic___at_Lean_Level_normalize___spec__1(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_142);
return x_159;
}
}
block_269:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; size_t x_175; size_t x_176; size_t x_177; size_t x_178; size_t x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_161);
x_162 = lean_st_ref_get(x_3, x_140);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_array_get_size(x_166);
x_168 = l_Lean_Level_hash(x_138);
x_169 = 32;
x_170 = lean_uint64_shift_right(x_168, x_169);
x_171 = lean_uint64_xor(x_168, x_170);
x_172 = 16;
x_173 = lean_uint64_shift_right(x_171, x_172);
x_174 = lean_uint64_xor(x_171, x_173);
x_175 = lean_uint64_to_usize(x_174);
x_176 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_177 = 1;
x_178 = lean_usize_sub(x_176, x_177);
x_179 = lean_usize_land(x_175, x_178);
x_180 = lean_array_uget(x_166, x_179);
lean_dec(x_166);
x_181 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_138, x_180);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_inc(x_138);
x_182 = l_Lean_Meta_Closure_collectLevelAux(x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_165);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_st_ref_take(x_3, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 5);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 6);
lean_inc(x_194);
x_195 = lean_ctor_get(x_186, 7);
lean_inc(x_195);
x_196 = lean_ctor_get(x_186, 8);
lean_inc(x_196);
x_197 = lean_ctor_get(x_186, 9);
lean_inc(x_197);
x_198 = lean_ctor_get(x_186, 10);
lean_inc(x_198);
x_199 = lean_ctor_get(x_186, 11);
lean_inc(x_199);
lean_dec(x_186);
x_200 = !lean_is_exclusive(x_187);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; size_t x_204; size_t x_205; size_t x_206; lean_object* x_207; uint8_t x_208; 
x_201 = lean_ctor_get(x_187, 0);
x_202 = lean_ctor_get(x_187, 1);
x_203 = lean_array_get_size(x_202);
x_204 = lean_usize_of_nat(x_203);
lean_dec(x_203);
x_205 = lean_usize_sub(x_204, x_177);
x_206 = lean_usize_land(x_175, x_205);
x_207 = lean_array_uget(x_202, x_206);
x_208 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_138, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_201, x_209);
lean_dec(x_201);
lean_inc(x_183);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_138);
lean_ctor_set(x_211, 1, x_183);
lean_ctor_set(x_211, 2, x_207);
x_212 = lean_array_uset(x_202, x_206, x_211);
x_213 = lean_unsigned_to_nat(4u);
x_214 = lean_nat_mul(x_210, x_213);
x_215 = lean_unsigned_to_nat(3u);
x_216 = lean_nat_div(x_214, x_215);
lean_dec(x_214);
x_217 = lean_array_get_size(x_212);
x_218 = lean_nat_dec_le(x_216, x_217);
lean_dec(x_217);
lean_dec(x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_212);
lean_ctor_set(x_187, 1, x_219);
lean_ctor_set(x_187, 0, x_210);
x_220 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_220, 0, x_187);
lean_ctor_set(x_220, 1, x_189);
lean_ctor_set(x_220, 2, x_190);
lean_ctor_set(x_220, 3, x_191);
lean_ctor_set(x_220, 4, x_192);
lean_ctor_set(x_220, 5, x_193);
lean_ctor_set(x_220, 6, x_194);
lean_ctor_set(x_220, 7, x_195);
lean_ctor_set(x_220, 8, x_196);
lean_ctor_set(x_220, 9, x_197);
lean_ctor_set(x_220, 10, x_198);
lean_ctor_set(x_220, 11, x_199);
x_221 = lean_st_ref_set(x_3, x_220, x_188);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_141 = x_183;
x_142 = x_222;
goto block_160;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_ctor_set(x_187, 1, x_212);
lean_ctor_set(x_187, 0, x_210);
x_223 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_223, 0, x_187);
lean_ctor_set(x_223, 1, x_189);
lean_ctor_set(x_223, 2, x_190);
lean_ctor_set(x_223, 3, x_191);
lean_ctor_set(x_223, 4, x_192);
lean_ctor_set(x_223, 5, x_193);
lean_ctor_set(x_223, 6, x_194);
lean_ctor_set(x_223, 7, x_195);
lean_ctor_set(x_223, 8, x_196);
lean_ctor_set(x_223, 9, x_197);
lean_ctor_set(x_223, 10, x_198);
lean_ctor_set(x_223, 11, x_199);
x_224 = lean_st_ref_set(x_3, x_223, x_188);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_141 = x_183;
x_142 = x_225;
goto block_160;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = lean_box(0);
x_227 = lean_array_uset(x_202, x_206, x_226);
lean_inc(x_183);
x_228 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_138, x_183, x_207);
x_229 = lean_array_uset(x_227, x_206, x_228);
lean_ctor_set(x_187, 1, x_229);
x_230 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_230, 0, x_187);
lean_ctor_set(x_230, 1, x_189);
lean_ctor_set(x_230, 2, x_190);
lean_ctor_set(x_230, 3, x_191);
lean_ctor_set(x_230, 4, x_192);
lean_ctor_set(x_230, 5, x_193);
lean_ctor_set(x_230, 6, x_194);
lean_ctor_set(x_230, 7, x_195);
lean_ctor_set(x_230, 8, x_196);
lean_ctor_set(x_230, 9, x_197);
lean_ctor_set(x_230, 10, x_198);
lean_ctor_set(x_230, 11, x_199);
x_231 = lean_st_ref_set(x_3, x_230, x_188);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_141 = x_183;
x_142 = x_232;
goto block_160;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; size_t x_236; size_t x_237; size_t x_238; lean_object* x_239; uint8_t x_240; 
x_233 = lean_ctor_get(x_187, 0);
x_234 = lean_ctor_get(x_187, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_187);
x_235 = lean_array_get_size(x_234);
x_236 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_237 = lean_usize_sub(x_236, x_177);
x_238 = lean_usize_land(x_175, x_237);
x_239 = lean_array_uget(x_234, x_238);
x_240 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_138, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_233, x_241);
lean_dec(x_233);
lean_inc(x_183);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_138);
lean_ctor_set(x_243, 1, x_183);
lean_ctor_set(x_243, 2, x_239);
x_244 = lean_array_uset(x_234, x_238, x_243);
x_245 = lean_unsigned_to_nat(4u);
x_246 = lean_nat_mul(x_242, x_245);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_nat_div(x_246, x_247);
lean_dec(x_246);
x_249 = lean_array_get_size(x_244);
x_250 = lean_nat_dec_le(x_248, x_249);
lean_dec(x_249);
lean_dec(x_248);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_251 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_244);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_242);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_189);
lean_ctor_set(x_253, 2, x_190);
lean_ctor_set(x_253, 3, x_191);
lean_ctor_set(x_253, 4, x_192);
lean_ctor_set(x_253, 5, x_193);
lean_ctor_set(x_253, 6, x_194);
lean_ctor_set(x_253, 7, x_195);
lean_ctor_set(x_253, 8, x_196);
lean_ctor_set(x_253, 9, x_197);
lean_ctor_set(x_253, 10, x_198);
lean_ctor_set(x_253, 11, x_199);
x_254 = lean_st_ref_set(x_3, x_253, x_188);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_141 = x_183;
x_142 = x_255;
goto block_160;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_242);
lean_ctor_set(x_256, 1, x_244);
x_257 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_189);
lean_ctor_set(x_257, 2, x_190);
lean_ctor_set(x_257, 3, x_191);
lean_ctor_set(x_257, 4, x_192);
lean_ctor_set(x_257, 5, x_193);
lean_ctor_set(x_257, 6, x_194);
lean_ctor_set(x_257, 7, x_195);
lean_ctor_set(x_257, 8, x_196);
lean_ctor_set(x_257, 9, x_197);
lean_ctor_set(x_257, 10, x_198);
lean_ctor_set(x_257, 11, x_199);
x_258 = lean_st_ref_set(x_3, x_257, x_188);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_141 = x_183;
x_142 = x_259;
goto block_160;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_box(0);
x_261 = lean_array_uset(x_234, x_238, x_260);
lean_inc(x_183);
x_262 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_138, x_183, x_239);
x_263 = lean_array_uset(x_261, x_238, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_233);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_189);
lean_ctor_set(x_265, 2, x_190);
lean_ctor_set(x_265, 3, x_191);
lean_ctor_set(x_265, 4, x_192);
lean_ctor_set(x_265, 5, x_193);
lean_ctor_set(x_265, 6, x_194);
lean_ctor_set(x_265, 7, x_195);
lean_ctor_set(x_265, 8, x_196);
lean_ctor_set(x_265, 9, x_197);
lean_ctor_set(x_265, 10, x_198);
lean_ctor_set(x_265, 11, x_199);
x_266 = lean_st_ref_set(x_3, x_265, x_188);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_141 = x_183;
x_142 = x_267;
goto block_160;
}
}
}
else
{
lean_object* x_268; 
lean_dec(x_138);
x_268 = lean_ctor_get(x_181, 0);
lean_inc(x_268);
lean_dec(x_181);
x_141 = x_268;
x_142 = x_165;
goto block_160;
}
}
}
block_383:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint64_t x_282; uint64_t x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; uint64_t x_287; uint64_t x_288; size_t x_289; size_t x_290; size_t x_291; size_t x_292; size_t x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_275);
x_276 = lean_st_ref_get(x_3, x_8);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_array_get_size(x_280);
x_282 = l_Lean_Level_hash(x_137);
x_283 = 32;
x_284 = lean_uint64_shift_right(x_282, x_283);
x_285 = lean_uint64_xor(x_282, x_284);
x_286 = 16;
x_287 = lean_uint64_shift_right(x_285, x_286);
x_288 = lean_uint64_xor(x_285, x_287);
x_289 = lean_uint64_to_usize(x_288);
x_290 = lean_usize_of_nat(x_281);
lean_dec(x_281);
x_291 = 1;
x_292 = lean_usize_sub(x_290, x_291);
x_293 = lean_usize_land(x_289, x_292);
x_294 = lean_array_uget(x_280, x_293);
lean_dec(x_280);
x_295 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_137, x_294);
lean_dec(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
lean_inc(x_137);
x_296 = l_Lean_Meta_Closure_collectLevelAux(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_279);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_st_ref_take(x_3, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_300, 2);
lean_inc(x_304);
x_305 = lean_ctor_get(x_300, 3);
lean_inc(x_305);
x_306 = lean_ctor_get(x_300, 4);
lean_inc(x_306);
x_307 = lean_ctor_get(x_300, 5);
lean_inc(x_307);
x_308 = lean_ctor_get(x_300, 6);
lean_inc(x_308);
x_309 = lean_ctor_get(x_300, 7);
lean_inc(x_309);
x_310 = lean_ctor_get(x_300, 8);
lean_inc(x_310);
x_311 = lean_ctor_get(x_300, 9);
lean_inc(x_311);
x_312 = lean_ctor_get(x_300, 10);
lean_inc(x_312);
x_313 = lean_ctor_get(x_300, 11);
lean_inc(x_313);
lean_dec(x_300);
x_314 = !lean_is_exclusive(x_301);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; size_t x_318; size_t x_319; size_t x_320; lean_object* x_321; uint8_t x_322; 
x_315 = lean_ctor_get(x_301, 0);
x_316 = lean_ctor_get(x_301, 1);
x_317 = lean_array_get_size(x_316);
x_318 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_319 = lean_usize_sub(x_318, x_291);
x_320 = lean_usize_land(x_289, x_319);
x_321 = lean_array_uget(x_316, x_320);
x_322 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_137, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_nat_add(x_315, x_323);
lean_dec(x_315);
lean_inc(x_297);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_137);
lean_ctor_set(x_325, 1, x_297);
lean_ctor_set(x_325, 2, x_321);
x_326 = lean_array_uset(x_316, x_320, x_325);
x_327 = lean_unsigned_to_nat(4u);
x_328 = lean_nat_mul(x_324, x_327);
x_329 = lean_unsigned_to_nat(3u);
x_330 = lean_nat_div(x_328, x_329);
lean_dec(x_328);
x_331 = lean_array_get_size(x_326);
x_332 = lean_nat_dec_le(x_330, x_331);
lean_dec(x_331);
lean_dec(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_326);
lean_ctor_set(x_301, 1, x_333);
lean_ctor_set(x_301, 0, x_324);
x_334 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_334, 0, x_301);
lean_ctor_set(x_334, 1, x_303);
lean_ctor_set(x_334, 2, x_304);
lean_ctor_set(x_334, 3, x_305);
lean_ctor_set(x_334, 4, x_306);
lean_ctor_set(x_334, 5, x_307);
lean_ctor_set(x_334, 6, x_308);
lean_ctor_set(x_334, 7, x_309);
lean_ctor_set(x_334, 8, x_310);
lean_ctor_set(x_334, 9, x_311);
lean_ctor_set(x_334, 10, x_312);
lean_ctor_set(x_334, 11, x_313);
x_335 = lean_st_ref_set(x_3, x_334, x_302);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_139 = x_297;
x_140 = x_336;
goto block_274;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_ctor_set(x_301, 1, x_326);
lean_ctor_set(x_301, 0, x_324);
x_337 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_337, 0, x_301);
lean_ctor_set(x_337, 1, x_303);
lean_ctor_set(x_337, 2, x_304);
lean_ctor_set(x_337, 3, x_305);
lean_ctor_set(x_337, 4, x_306);
lean_ctor_set(x_337, 5, x_307);
lean_ctor_set(x_337, 6, x_308);
lean_ctor_set(x_337, 7, x_309);
lean_ctor_set(x_337, 8, x_310);
lean_ctor_set(x_337, 9, x_311);
lean_ctor_set(x_337, 10, x_312);
lean_ctor_set(x_337, 11, x_313);
x_338 = lean_st_ref_set(x_3, x_337, x_302);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_139 = x_297;
x_140 = x_339;
goto block_274;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_340 = lean_box(0);
x_341 = lean_array_uset(x_316, x_320, x_340);
lean_inc(x_297);
x_342 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_137, x_297, x_321);
x_343 = lean_array_uset(x_341, x_320, x_342);
lean_ctor_set(x_301, 1, x_343);
x_344 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_344, 0, x_301);
lean_ctor_set(x_344, 1, x_303);
lean_ctor_set(x_344, 2, x_304);
lean_ctor_set(x_344, 3, x_305);
lean_ctor_set(x_344, 4, x_306);
lean_ctor_set(x_344, 5, x_307);
lean_ctor_set(x_344, 6, x_308);
lean_ctor_set(x_344, 7, x_309);
lean_ctor_set(x_344, 8, x_310);
lean_ctor_set(x_344, 9, x_311);
lean_ctor_set(x_344, 10, x_312);
lean_ctor_set(x_344, 11, x_313);
x_345 = lean_st_ref_set(x_3, x_344, x_302);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_139 = x_297;
x_140 = x_346;
goto block_274;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; size_t x_350; size_t x_351; size_t x_352; lean_object* x_353; uint8_t x_354; 
x_347 = lean_ctor_get(x_301, 0);
x_348 = lean_ctor_get(x_301, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_301);
x_349 = lean_array_get_size(x_348);
x_350 = lean_usize_of_nat(x_349);
lean_dec(x_349);
x_351 = lean_usize_sub(x_350, x_291);
x_352 = lean_usize_land(x_289, x_351);
x_353 = lean_array_uget(x_348, x_352);
x_354 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_137, x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_nat_add(x_347, x_355);
lean_dec(x_347);
lean_inc(x_297);
x_357 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_357, 0, x_137);
lean_ctor_set(x_357, 1, x_297);
lean_ctor_set(x_357, 2, x_353);
x_358 = lean_array_uset(x_348, x_352, x_357);
x_359 = lean_unsigned_to_nat(4u);
x_360 = lean_nat_mul(x_356, x_359);
x_361 = lean_unsigned_to_nat(3u);
x_362 = lean_nat_div(x_360, x_361);
lean_dec(x_360);
x_363 = lean_array_get_size(x_358);
x_364 = lean_nat_dec_le(x_362, x_363);
lean_dec(x_363);
lean_dec(x_362);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_365 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_358);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_356);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_303);
lean_ctor_set(x_367, 2, x_304);
lean_ctor_set(x_367, 3, x_305);
lean_ctor_set(x_367, 4, x_306);
lean_ctor_set(x_367, 5, x_307);
lean_ctor_set(x_367, 6, x_308);
lean_ctor_set(x_367, 7, x_309);
lean_ctor_set(x_367, 8, x_310);
lean_ctor_set(x_367, 9, x_311);
lean_ctor_set(x_367, 10, x_312);
lean_ctor_set(x_367, 11, x_313);
x_368 = lean_st_ref_set(x_3, x_367, x_302);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_139 = x_297;
x_140 = x_369;
goto block_274;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_356);
lean_ctor_set(x_370, 1, x_358);
x_371 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_303);
lean_ctor_set(x_371, 2, x_304);
lean_ctor_set(x_371, 3, x_305);
lean_ctor_set(x_371, 4, x_306);
lean_ctor_set(x_371, 5, x_307);
lean_ctor_set(x_371, 6, x_308);
lean_ctor_set(x_371, 7, x_309);
lean_ctor_set(x_371, 8, x_310);
lean_ctor_set(x_371, 9, x_311);
lean_ctor_set(x_371, 10, x_312);
lean_ctor_set(x_371, 11, x_313);
x_372 = lean_st_ref_set(x_3, x_371, x_302);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_139 = x_297;
x_140 = x_373;
goto block_274;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_374 = lean_box(0);
x_375 = lean_array_uset(x_348, x_352, x_374);
lean_inc(x_297);
x_376 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_137, x_297, x_353);
x_377 = lean_array_uset(x_375, x_352, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_347);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_303);
lean_ctor_set(x_379, 2, x_304);
lean_ctor_set(x_379, 3, x_305);
lean_ctor_set(x_379, 4, x_306);
lean_ctor_set(x_379, 5, x_307);
lean_ctor_set(x_379, 6, x_308);
lean_ctor_set(x_379, 7, x_309);
lean_ctor_set(x_379, 8, x_310);
lean_ctor_set(x_379, 9, x_311);
lean_ctor_set(x_379, 10, x_312);
lean_ctor_set(x_379, 11, x_313);
x_380 = lean_st_ref_set(x_3, x_379, x_302);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_139 = x_297;
x_140 = x_381;
goto block_274;
}
}
}
else
{
lean_object* x_382; 
lean_dec(x_137);
x_382 = lean_ctor_get(x_295, 0);
lean_inc(x_382);
lean_dec(x_295);
x_139 = x_382;
x_140 = x_279;
goto block_274;
}
}
}
case 3:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_526; uint8_t x_635; 
x_388 = lean_ctor_get(x_1, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_1, 1);
lean_inc(x_389);
x_635 = l_Lean_Level_hasMVar(x_388);
if (x_635 == 0)
{
uint8_t x_636; 
x_636 = l_Lean_Level_hasParam(x_388);
if (x_636 == 0)
{
x_390 = x_388;
x_391 = x_8;
goto block_525;
}
else
{
lean_object* x_637; 
x_637 = lean_box(0);
x_526 = x_637;
goto block_634;
}
}
else
{
lean_object* x_638; 
x_638 = lean_box(0);
x_526 = x_638;
goto block_634;
}
block_525:
{
lean_object* x_392; lean_object* x_393; lean_object* x_412; uint8_t x_521; 
x_521 = l_Lean_Level_hasMVar(x_389);
if (x_521 == 0)
{
uint8_t x_522; 
x_522 = l_Lean_Level_hasParam(x_389);
if (x_522 == 0)
{
x_392 = x_389;
x_393 = x_391;
goto block_411;
}
else
{
lean_object* x_523; 
x_523 = lean_box(0);
x_412 = x_523;
goto block_520;
}
}
else
{
lean_object* x_524; 
x_524 = lean_box(0);
x_412 = x_524;
goto block_520;
}
block_411:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_394; lean_object* x_395; size_t x_396; size_t x_397; uint8_t x_398; 
x_394 = lean_ctor_get(x_1, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_1, 1);
lean_inc(x_395);
x_396 = lean_ptr_addr(x_394);
lean_dec(x_394);
x_397 = lean_ptr_addr(x_390);
x_398 = lean_usize_dec_eq(x_396, x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
lean_dec(x_395);
lean_dec(x_1);
x_399 = l_Lean_mkLevelIMax_x27(x_390, x_392);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_393);
return x_400;
}
else
{
size_t x_401; size_t x_402; uint8_t x_403; 
x_401 = lean_ptr_addr(x_395);
lean_dec(x_395);
x_402 = lean_ptr_addr(x_392);
x_403 = lean_usize_dec_eq(x_401, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_1);
x_404 = l_Lean_mkLevelIMax_x27(x_390, x_392);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_393);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = l_Lean_simpLevelIMax_x27(x_390, x_392, x_1);
lean_dec(x_1);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_393);
return x_407;
}
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_1);
x_408 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_409 = l_panic___at_Lean_Level_normalize___spec__1(x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_393);
return x_410;
}
}
block_520:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint64_t x_419; uint64_t x_420; uint64_t x_421; uint64_t x_422; uint64_t x_423; uint64_t x_424; uint64_t x_425; size_t x_426; size_t x_427; size_t x_428; size_t x_429; size_t x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_412);
x_413 = lean_st_ref_get(x_3, x_391);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
lean_dec(x_413);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_array_get_size(x_417);
x_419 = l_Lean_Level_hash(x_389);
x_420 = 32;
x_421 = lean_uint64_shift_right(x_419, x_420);
x_422 = lean_uint64_xor(x_419, x_421);
x_423 = 16;
x_424 = lean_uint64_shift_right(x_422, x_423);
x_425 = lean_uint64_xor(x_422, x_424);
x_426 = lean_uint64_to_usize(x_425);
x_427 = lean_usize_of_nat(x_418);
lean_dec(x_418);
x_428 = 1;
x_429 = lean_usize_sub(x_427, x_428);
x_430 = lean_usize_land(x_426, x_429);
x_431 = lean_array_uget(x_417, x_430);
lean_dec(x_417);
x_432 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_389, x_431);
lean_dec(x_431);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_inc(x_389);
x_433 = l_Lean_Meta_Closure_collectLevelAux(x_389, x_2, x_3, x_4, x_5, x_6, x_7, x_416);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_st_ref_take(x_3, x_435);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_437, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_437, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_437, 4);
lean_inc(x_443);
x_444 = lean_ctor_get(x_437, 5);
lean_inc(x_444);
x_445 = lean_ctor_get(x_437, 6);
lean_inc(x_445);
x_446 = lean_ctor_get(x_437, 7);
lean_inc(x_446);
x_447 = lean_ctor_get(x_437, 8);
lean_inc(x_447);
x_448 = lean_ctor_get(x_437, 9);
lean_inc(x_448);
x_449 = lean_ctor_get(x_437, 10);
lean_inc(x_449);
x_450 = lean_ctor_get(x_437, 11);
lean_inc(x_450);
lean_dec(x_437);
x_451 = !lean_is_exclusive(x_438);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; size_t x_455; size_t x_456; size_t x_457; lean_object* x_458; uint8_t x_459; 
x_452 = lean_ctor_get(x_438, 0);
x_453 = lean_ctor_get(x_438, 1);
x_454 = lean_array_get_size(x_453);
x_455 = lean_usize_of_nat(x_454);
lean_dec(x_454);
x_456 = lean_usize_sub(x_455, x_428);
x_457 = lean_usize_land(x_426, x_456);
x_458 = lean_array_uget(x_453, x_457);
x_459 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_389, x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_460 = lean_unsigned_to_nat(1u);
x_461 = lean_nat_add(x_452, x_460);
lean_dec(x_452);
lean_inc(x_434);
x_462 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_462, 0, x_389);
lean_ctor_set(x_462, 1, x_434);
lean_ctor_set(x_462, 2, x_458);
x_463 = lean_array_uset(x_453, x_457, x_462);
x_464 = lean_unsigned_to_nat(4u);
x_465 = lean_nat_mul(x_461, x_464);
x_466 = lean_unsigned_to_nat(3u);
x_467 = lean_nat_div(x_465, x_466);
lean_dec(x_465);
x_468 = lean_array_get_size(x_463);
x_469 = lean_nat_dec_le(x_467, x_468);
lean_dec(x_468);
lean_dec(x_467);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_463);
lean_ctor_set(x_438, 1, x_470);
lean_ctor_set(x_438, 0, x_461);
x_471 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_471, 0, x_438);
lean_ctor_set(x_471, 1, x_440);
lean_ctor_set(x_471, 2, x_441);
lean_ctor_set(x_471, 3, x_442);
lean_ctor_set(x_471, 4, x_443);
lean_ctor_set(x_471, 5, x_444);
lean_ctor_set(x_471, 6, x_445);
lean_ctor_set(x_471, 7, x_446);
lean_ctor_set(x_471, 8, x_447);
lean_ctor_set(x_471, 9, x_448);
lean_ctor_set(x_471, 10, x_449);
lean_ctor_set(x_471, 11, x_450);
x_472 = lean_st_ref_set(x_3, x_471, x_439);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_392 = x_434;
x_393 = x_473;
goto block_411;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_ctor_set(x_438, 1, x_463);
lean_ctor_set(x_438, 0, x_461);
x_474 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_474, 0, x_438);
lean_ctor_set(x_474, 1, x_440);
lean_ctor_set(x_474, 2, x_441);
lean_ctor_set(x_474, 3, x_442);
lean_ctor_set(x_474, 4, x_443);
lean_ctor_set(x_474, 5, x_444);
lean_ctor_set(x_474, 6, x_445);
lean_ctor_set(x_474, 7, x_446);
lean_ctor_set(x_474, 8, x_447);
lean_ctor_set(x_474, 9, x_448);
lean_ctor_set(x_474, 10, x_449);
lean_ctor_set(x_474, 11, x_450);
x_475 = lean_st_ref_set(x_3, x_474, x_439);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
lean_dec(x_475);
x_392 = x_434;
x_393 = x_476;
goto block_411;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_477 = lean_box(0);
x_478 = lean_array_uset(x_453, x_457, x_477);
lean_inc(x_434);
x_479 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_389, x_434, x_458);
x_480 = lean_array_uset(x_478, x_457, x_479);
lean_ctor_set(x_438, 1, x_480);
x_481 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_481, 0, x_438);
lean_ctor_set(x_481, 1, x_440);
lean_ctor_set(x_481, 2, x_441);
lean_ctor_set(x_481, 3, x_442);
lean_ctor_set(x_481, 4, x_443);
lean_ctor_set(x_481, 5, x_444);
lean_ctor_set(x_481, 6, x_445);
lean_ctor_set(x_481, 7, x_446);
lean_ctor_set(x_481, 8, x_447);
lean_ctor_set(x_481, 9, x_448);
lean_ctor_set(x_481, 10, x_449);
lean_ctor_set(x_481, 11, x_450);
x_482 = lean_st_ref_set(x_3, x_481, x_439);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
x_392 = x_434;
x_393 = x_483;
goto block_411;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; size_t x_487; size_t x_488; size_t x_489; lean_object* x_490; uint8_t x_491; 
x_484 = lean_ctor_get(x_438, 0);
x_485 = lean_ctor_get(x_438, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_438);
x_486 = lean_array_get_size(x_485);
x_487 = lean_usize_of_nat(x_486);
lean_dec(x_486);
x_488 = lean_usize_sub(x_487, x_428);
x_489 = lean_usize_land(x_426, x_488);
x_490 = lean_array_uget(x_485, x_489);
x_491 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_389, x_490);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_492 = lean_unsigned_to_nat(1u);
x_493 = lean_nat_add(x_484, x_492);
lean_dec(x_484);
lean_inc(x_434);
x_494 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_494, 0, x_389);
lean_ctor_set(x_494, 1, x_434);
lean_ctor_set(x_494, 2, x_490);
x_495 = lean_array_uset(x_485, x_489, x_494);
x_496 = lean_unsigned_to_nat(4u);
x_497 = lean_nat_mul(x_493, x_496);
x_498 = lean_unsigned_to_nat(3u);
x_499 = lean_nat_div(x_497, x_498);
lean_dec(x_497);
x_500 = lean_array_get_size(x_495);
x_501 = lean_nat_dec_le(x_499, x_500);
lean_dec(x_500);
lean_dec(x_499);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_502 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_495);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_493);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_440);
lean_ctor_set(x_504, 2, x_441);
lean_ctor_set(x_504, 3, x_442);
lean_ctor_set(x_504, 4, x_443);
lean_ctor_set(x_504, 5, x_444);
lean_ctor_set(x_504, 6, x_445);
lean_ctor_set(x_504, 7, x_446);
lean_ctor_set(x_504, 8, x_447);
lean_ctor_set(x_504, 9, x_448);
lean_ctor_set(x_504, 10, x_449);
lean_ctor_set(x_504, 11, x_450);
x_505 = lean_st_ref_set(x_3, x_504, x_439);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_392 = x_434;
x_393 = x_506;
goto block_411;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_493);
lean_ctor_set(x_507, 1, x_495);
x_508 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_440);
lean_ctor_set(x_508, 2, x_441);
lean_ctor_set(x_508, 3, x_442);
lean_ctor_set(x_508, 4, x_443);
lean_ctor_set(x_508, 5, x_444);
lean_ctor_set(x_508, 6, x_445);
lean_ctor_set(x_508, 7, x_446);
lean_ctor_set(x_508, 8, x_447);
lean_ctor_set(x_508, 9, x_448);
lean_ctor_set(x_508, 10, x_449);
lean_ctor_set(x_508, 11, x_450);
x_509 = lean_st_ref_set(x_3, x_508, x_439);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
lean_dec(x_509);
x_392 = x_434;
x_393 = x_510;
goto block_411;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_511 = lean_box(0);
x_512 = lean_array_uset(x_485, x_489, x_511);
lean_inc(x_434);
x_513 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_389, x_434, x_490);
x_514 = lean_array_uset(x_512, x_489, x_513);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_484);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_440);
lean_ctor_set(x_516, 2, x_441);
lean_ctor_set(x_516, 3, x_442);
lean_ctor_set(x_516, 4, x_443);
lean_ctor_set(x_516, 5, x_444);
lean_ctor_set(x_516, 6, x_445);
lean_ctor_set(x_516, 7, x_446);
lean_ctor_set(x_516, 8, x_447);
lean_ctor_set(x_516, 9, x_448);
lean_ctor_set(x_516, 10, x_449);
lean_ctor_set(x_516, 11, x_450);
x_517 = lean_st_ref_set(x_3, x_516, x_439);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
lean_dec(x_517);
x_392 = x_434;
x_393 = x_518;
goto block_411;
}
}
}
else
{
lean_object* x_519; 
lean_dec(x_389);
x_519 = lean_ctor_get(x_432, 0);
lean_inc(x_519);
lean_dec(x_432);
x_392 = x_519;
x_393 = x_416;
goto block_411;
}
}
}
block_634:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint64_t x_533; uint64_t x_534; uint64_t x_535; uint64_t x_536; uint64_t x_537; uint64_t x_538; uint64_t x_539; size_t x_540; size_t x_541; size_t x_542; size_t x_543; size_t x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_526);
x_527 = lean_st_ref_get(x_3, x_8);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_ctor_get(x_527, 1);
lean_inc(x_530);
lean_dec(x_527);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_array_get_size(x_531);
x_533 = l_Lean_Level_hash(x_388);
x_534 = 32;
x_535 = lean_uint64_shift_right(x_533, x_534);
x_536 = lean_uint64_xor(x_533, x_535);
x_537 = 16;
x_538 = lean_uint64_shift_right(x_536, x_537);
x_539 = lean_uint64_xor(x_536, x_538);
x_540 = lean_uint64_to_usize(x_539);
x_541 = lean_usize_of_nat(x_532);
lean_dec(x_532);
x_542 = 1;
x_543 = lean_usize_sub(x_541, x_542);
x_544 = lean_usize_land(x_540, x_543);
x_545 = lean_array_uget(x_531, x_544);
lean_dec(x_531);
x_546 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_388, x_545);
lean_dec(x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
lean_inc(x_388);
x_547 = l_Lean_Meta_Closure_collectLevelAux(x_388, x_2, x_3, x_4, x_5, x_6, x_7, x_530);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_550 = lean_st_ref_take(x_3, x_549);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_550, 1);
lean_inc(x_553);
lean_dec(x_550);
x_554 = lean_ctor_get(x_551, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_551, 2);
lean_inc(x_555);
x_556 = lean_ctor_get(x_551, 3);
lean_inc(x_556);
x_557 = lean_ctor_get(x_551, 4);
lean_inc(x_557);
x_558 = lean_ctor_get(x_551, 5);
lean_inc(x_558);
x_559 = lean_ctor_get(x_551, 6);
lean_inc(x_559);
x_560 = lean_ctor_get(x_551, 7);
lean_inc(x_560);
x_561 = lean_ctor_get(x_551, 8);
lean_inc(x_561);
x_562 = lean_ctor_get(x_551, 9);
lean_inc(x_562);
x_563 = lean_ctor_get(x_551, 10);
lean_inc(x_563);
x_564 = lean_ctor_get(x_551, 11);
lean_inc(x_564);
lean_dec(x_551);
x_565 = !lean_is_exclusive(x_552);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; size_t x_569; size_t x_570; size_t x_571; lean_object* x_572; uint8_t x_573; 
x_566 = lean_ctor_get(x_552, 0);
x_567 = lean_ctor_get(x_552, 1);
x_568 = lean_array_get_size(x_567);
x_569 = lean_usize_of_nat(x_568);
lean_dec(x_568);
x_570 = lean_usize_sub(x_569, x_542);
x_571 = lean_usize_land(x_540, x_570);
x_572 = lean_array_uget(x_567, x_571);
x_573 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_388, x_572);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_574 = lean_unsigned_to_nat(1u);
x_575 = lean_nat_add(x_566, x_574);
lean_dec(x_566);
lean_inc(x_548);
x_576 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_576, 0, x_388);
lean_ctor_set(x_576, 1, x_548);
lean_ctor_set(x_576, 2, x_572);
x_577 = lean_array_uset(x_567, x_571, x_576);
x_578 = lean_unsigned_to_nat(4u);
x_579 = lean_nat_mul(x_575, x_578);
x_580 = lean_unsigned_to_nat(3u);
x_581 = lean_nat_div(x_579, x_580);
lean_dec(x_579);
x_582 = lean_array_get_size(x_577);
x_583 = lean_nat_dec_le(x_581, x_582);
lean_dec(x_582);
lean_dec(x_581);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_584 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_577);
lean_ctor_set(x_552, 1, x_584);
lean_ctor_set(x_552, 0, x_575);
x_585 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_585, 0, x_552);
lean_ctor_set(x_585, 1, x_554);
lean_ctor_set(x_585, 2, x_555);
lean_ctor_set(x_585, 3, x_556);
lean_ctor_set(x_585, 4, x_557);
lean_ctor_set(x_585, 5, x_558);
lean_ctor_set(x_585, 6, x_559);
lean_ctor_set(x_585, 7, x_560);
lean_ctor_set(x_585, 8, x_561);
lean_ctor_set(x_585, 9, x_562);
lean_ctor_set(x_585, 10, x_563);
lean_ctor_set(x_585, 11, x_564);
x_586 = lean_st_ref_set(x_3, x_585, x_553);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
x_390 = x_548;
x_391 = x_587;
goto block_525;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_ctor_set(x_552, 1, x_577);
lean_ctor_set(x_552, 0, x_575);
x_588 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_588, 0, x_552);
lean_ctor_set(x_588, 1, x_554);
lean_ctor_set(x_588, 2, x_555);
lean_ctor_set(x_588, 3, x_556);
lean_ctor_set(x_588, 4, x_557);
lean_ctor_set(x_588, 5, x_558);
lean_ctor_set(x_588, 6, x_559);
lean_ctor_set(x_588, 7, x_560);
lean_ctor_set(x_588, 8, x_561);
lean_ctor_set(x_588, 9, x_562);
lean_ctor_set(x_588, 10, x_563);
lean_ctor_set(x_588, 11, x_564);
x_589 = lean_st_ref_set(x_3, x_588, x_553);
x_590 = lean_ctor_get(x_589, 1);
lean_inc(x_590);
lean_dec(x_589);
x_390 = x_548;
x_391 = x_590;
goto block_525;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_591 = lean_box(0);
x_592 = lean_array_uset(x_567, x_571, x_591);
lean_inc(x_548);
x_593 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_388, x_548, x_572);
x_594 = lean_array_uset(x_592, x_571, x_593);
lean_ctor_set(x_552, 1, x_594);
x_595 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_595, 0, x_552);
lean_ctor_set(x_595, 1, x_554);
lean_ctor_set(x_595, 2, x_555);
lean_ctor_set(x_595, 3, x_556);
lean_ctor_set(x_595, 4, x_557);
lean_ctor_set(x_595, 5, x_558);
lean_ctor_set(x_595, 6, x_559);
lean_ctor_set(x_595, 7, x_560);
lean_ctor_set(x_595, 8, x_561);
lean_ctor_set(x_595, 9, x_562);
lean_ctor_set(x_595, 10, x_563);
lean_ctor_set(x_595, 11, x_564);
x_596 = lean_st_ref_set(x_3, x_595, x_553);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_390 = x_548;
x_391 = x_597;
goto block_525;
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; size_t x_601; size_t x_602; size_t x_603; lean_object* x_604; uint8_t x_605; 
x_598 = lean_ctor_get(x_552, 0);
x_599 = lean_ctor_get(x_552, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_552);
x_600 = lean_array_get_size(x_599);
x_601 = lean_usize_of_nat(x_600);
lean_dec(x_600);
x_602 = lean_usize_sub(x_601, x_542);
x_603 = lean_usize_land(x_540, x_602);
x_604 = lean_array_uget(x_599, x_603);
x_605 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_388, x_604);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_598, x_606);
lean_dec(x_598);
lean_inc(x_548);
x_608 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_608, 0, x_388);
lean_ctor_set(x_608, 1, x_548);
lean_ctor_set(x_608, 2, x_604);
x_609 = lean_array_uset(x_599, x_603, x_608);
x_610 = lean_unsigned_to_nat(4u);
x_611 = lean_nat_mul(x_607, x_610);
x_612 = lean_unsigned_to_nat(3u);
x_613 = lean_nat_div(x_611, x_612);
lean_dec(x_611);
x_614 = lean_array_get_size(x_609);
x_615 = lean_nat_dec_le(x_613, x_614);
lean_dec(x_614);
lean_dec(x_613);
if (x_615 == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_616 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_609);
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_607);
lean_ctor_set(x_617, 1, x_616);
x_618 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_554);
lean_ctor_set(x_618, 2, x_555);
lean_ctor_set(x_618, 3, x_556);
lean_ctor_set(x_618, 4, x_557);
lean_ctor_set(x_618, 5, x_558);
lean_ctor_set(x_618, 6, x_559);
lean_ctor_set(x_618, 7, x_560);
lean_ctor_set(x_618, 8, x_561);
lean_ctor_set(x_618, 9, x_562);
lean_ctor_set(x_618, 10, x_563);
lean_ctor_set(x_618, 11, x_564);
x_619 = lean_st_ref_set(x_3, x_618, x_553);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
x_390 = x_548;
x_391 = x_620;
goto block_525;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_607);
lean_ctor_set(x_621, 1, x_609);
x_622 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_554);
lean_ctor_set(x_622, 2, x_555);
lean_ctor_set(x_622, 3, x_556);
lean_ctor_set(x_622, 4, x_557);
lean_ctor_set(x_622, 5, x_558);
lean_ctor_set(x_622, 6, x_559);
lean_ctor_set(x_622, 7, x_560);
lean_ctor_set(x_622, 8, x_561);
lean_ctor_set(x_622, 9, x_562);
lean_ctor_set(x_622, 10, x_563);
lean_ctor_set(x_622, 11, x_564);
x_623 = lean_st_ref_set(x_3, x_622, x_553);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
lean_dec(x_623);
x_390 = x_548;
x_391 = x_624;
goto block_525;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_625 = lean_box(0);
x_626 = lean_array_uset(x_599, x_603, x_625);
lean_inc(x_548);
x_627 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_388, x_548, x_604);
x_628 = lean_array_uset(x_626, x_603, x_627);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_598);
lean_ctor_set(x_629, 1, x_628);
x_630 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_554);
lean_ctor_set(x_630, 2, x_555);
lean_ctor_set(x_630, 3, x_556);
lean_ctor_set(x_630, 4, x_557);
lean_ctor_set(x_630, 5, x_558);
lean_ctor_set(x_630, 6, x_559);
lean_ctor_set(x_630, 7, x_560);
lean_ctor_set(x_630, 8, x_561);
lean_ctor_set(x_630, 9, x_562);
lean_ctor_set(x_630, 10, x_563);
lean_ctor_set(x_630, 11, x_564);
x_631 = lean_st_ref_set(x_3, x_630, x_553);
x_632 = lean_ctor_get(x_631, 1);
lean_inc(x_632);
lean_dec(x_631);
x_390 = x_548;
x_391 = x_632;
goto block_525;
}
}
}
else
{
lean_object* x_633; 
lean_dec(x_388);
x_633 = lean_ctor_get(x_546, 0);
lean_inc(x_633);
lean_dec(x_546);
x_390 = x_633;
x_391 = x_530;
goto block_525;
}
}
}
default: 
{
lean_object* x_639; 
x_639 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_639;
}
}
block_21:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_11; size_t x_12; size_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_13 = lean_ptr_addr(x_9);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_Level_succ___override(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_18 = l_Lean_Meta_Closure_collectLevelAux___closed__4;
x_19 = l_panic___at_Lean_Level_normalize___spec__1(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_253; 
x_253 = l_Lean_Level_hasMVar(x_1);
if (x_253 == 0)
{
uint8_t x_254; 
x_254 = l_Lean_Level_hasParam(x_1);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_1);
lean_ctor_set(x_255, 1, x_8);
return x_255;
}
else
{
lean_object* x_256; 
x_256 = lean_box(0);
x_9 = x_256;
goto block_252;
}
}
else
{
lean_object* x_257; 
x_257 = lean_box(0);
x_9 = x_257;
goto block_252;
}
block_252:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Level_hash(x_1);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
lean_dec(x_16);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_1, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_free_object(x_10);
lean_inc(x_1);
x_32 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_take(x_3, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_usize_sub(x_45, x_27);
x_47 = lean_usize_land(x_25, x_46);
x_48 = lean_array_uget(x_43, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_dec(x_42);
lean_inc(x_33);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_33);
lean_ctor_set(x_52, 2, x_48);
x_53 = lean_array_uset(x_43, x_47, x_52);
x_54 = lean_unsigned_to_nat(4u);
x_55 = lean_nat_mul(x_51, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_div(x_55, x_56);
lean_dec(x_55);
x_58 = lean_array_get_size(x_53);
x_59 = lean_nat_dec_le(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_53);
lean_ctor_set(x_37, 1, x_60);
lean_ctor_set(x_37, 0, x_51);
x_61 = lean_st_ref_set(x_3, x_36, x_38);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_33);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_33);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_ctor_set(x_37, 1, x_53);
lean_ctor_set(x_37, 0, x_51);
x_66 = lean_st_ref_set(x_3, x_36, x_38);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_33);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_33);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_43, x_47, x_71);
lean_inc(x_33);
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_33, x_48);
x_74 = lean_array_uset(x_72, x_47, x_73);
lean_ctor_set(x_37, 1, x_74);
x_75 = lean_st_ref_set(x_3, x_36, x_38);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_33);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_33);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_37, 0);
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_37);
x_82 = lean_array_get_size(x_81);
x_83 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_84 = lean_usize_sub(x_83, x_27);
x_85 = lean_usize_land(x_25, x_84);
x_86 = lean_array_uget(x_81, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_80, x_88);
lean_dec(x_80);
lean_inc(x_33);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_33);
lean_ctor_set(x_90, 2, x_86);
x_91 = lean_array_uset(x_81, x_85, x_90);
x_92 = lean_unsigned_to_nat(4u);
x_93 = lean_nat_mul(x_89, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_36, 0, x_99);
x_100 = lean_st_ref_set(x_3, x_36, x_38);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_33);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_91);
lean_ctor_set(x_36, 0, x_104);
x_105 = lean_st_ref_set(x_3, x_36, x_38);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_33);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_box(0);
x_110 = lean_array_uset(x_81, x_85, x_109);
lean_inc(x_33);
x_111 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_33, x_86);
x_112 = lean_array_uset(x_110, x_85, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_80);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_36, 0, x_113);
x_114 = lean_st_ref_set(x_3, x_36, x_38);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_33);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; uint8_t x_137; 
x_118 = lean_ctor_get(x_36, 1);
x_119 = lean_ctor_get(x_36, 2);
x_120 = lean_ctor_get(x_36, 3);
x_121 = lean_ctor_get(x_36, 4);
x_122 = lean_ctor_get(x_36, 5);
x_123 = lean_ctor_get(x_36, 6);
x_124 = lean_ctor_get(x_36, 7);
x_125 = lean_ctor_get(x_36, 8);
x_126 = lean_ctor_get(x_36, 9);
x_127 = lean_ctor_get(x_36, 10);
x_128 = lean_ctor_get(x_36, 11);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_36);
x_129 = lean_ctor_get(x_37, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_37, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_131 = x_37;
} else {
 lean_dec_ref(x_37);
 x_131 = lean_box(0);
}
x_132 = lean_array_get_size(x_130);
x_133 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_134 = lean_usize_sub(x_133, x_27);
x_135 = lean_usize_land(x_25, x_134);
x_136 = lean_array_uget(x_130, x_135);
x_137 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_129, x_138);
lean_dec(x_129);
lean_inc(x_33);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_33);
lean_ctor_set(x_140, 2, x_136);
x_141 = lean_array_uset(x_130, x_135, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_139, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_141);
if (lean_is_scalar(x_131)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_131;
}
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_118);
lean_ctor_set(x_150, 2, x_119);
lean_ctor_set(x_150, 3, x_120);
lean_ctor_set(x_150, 4, x_121);
lean_ctor_set(x_150, 5, x_122);
lean_ctor_set(x_150, 6, x_123);
lean_ctor_set(x_150, 7, x_124);
lean_ctor_set(x_150, 8, x_125);
lean_ctor_set(x_150, 9, x_126);
lean_ctor_set(x_150, 10, x_127);
lean_ctor_set(x_150, 11, x_128);
x_151 = lean_st_ref_set(x_3, x_150, x_38);
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
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_33);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_scalar(x_131)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_131;
}
lean_ctor_set(x_155, 0, x_139);
lean_ctor_set(x_155, 1, x_141);
x_156 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_118);
lean_ctor_set(x_156, 2, x_119);
lean_ctor_set(x_156, 3, x_120);
lean_ctor_set(x_156, 4, x_121);
lean_ctor_set(x_156, 5, x_122);
lean_ctor_set(x_156, 6, x_123);
lean_ctor_set(x_156, 7, x_124);
lean_ctor_set(x_156, 8, x_125);
lean_ctor_set(x_156, 9, x_126);
lean_ctor_set(x_156, 10, x_127);
lean_ctor_set(x_156, 11, x_128);
x_157 = lean_st_ref_set(x_3, x_156, x_38);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_33);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_box(0);
x_162 = lean_array_uset(x_130, x_135, x_161);
lean_inc(x_33);
x_163 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_33, x_136);
x_164 = lean_array_uset(x_162, x_135, x_163);
if (lean_is_scalar(x_131)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_131;
}
lean_ctor_set(x_165, 0, x_129);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_118);
lean_ctor_set(x_166, 2, x_119);
lean_ctor_set(x_166, 3, x_120);
lean_ctor_set(x_166, 4, x_121);
lean_ctor_set(x_166, 5, x_122);
lean_ctor_set(x_166, 6, x_123);
lean_ctor_set(x_166, 7, x_124);
lean_ctor_set(x_166, 8, x_125);
lean_ctor_set(x_166, 9, x_126);
lean_ctor_set(x_166, 10, x_127);
lean_ctor_set(x_166, 11, x_128);
x_167 = lean_st_ref_set(x_3, x_166, x_38);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_33);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_31, 0);
lean_inc(x_171);
lean_dec(x_31);
lean_ctor_set(x_10, 0, x_171);
return x_10;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; size_t x_182; size_t x_183; size_t x_184; size_t x_185; size_t x_186; lean_object* x_187; lean_object* x_188; 
x_172 = lean_ctor_get(x_10, 1);
lean_inc(x_172);
lean_dec(x_10);
x_173 = lean_ctor_get(x_12, 1);
lean_inc(x_173);
lean_dec(x_12);
x_174 = lean_array_get_size(x_173);
x_175 = l_Lean_Level_hash(x_1);
x_176 = 32;
x_177 = lean_uint64_shift_right(x_175, x_176);
x_178 = lean_uint64_xor(x_175, x_177);
x_179 = 16;
x_180 = lean_uint64_shift_right(x_178, x_179);
x_181 = lean_uint64_xor(x_178, x_180);
x_182 = lean_uint64_to_usize(x_181);
x_183 = lean_usize_of_nat(x_174);
lean_dec(x_174);
x_184 = 1;
x_185 = lean_usize_sub(x_183, x_184);
x_186 = lean_usize_land(x_182, x_185);
x_187 = lean_array_uget(x_173, x_186);
lean_dec(x_173);
x_188 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_1, x_187);
lean_dec(x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; size_t x_212; size_t x_213; size_t x_214; lean_object* x_215; uint8_t x_216; 
lean_inc(x_1);
x_189 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_172);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_st_ref_take(x_3, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 5);
lean_inc(x_200);
x_201 = lean_ctor_get(x_193, 6);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 7);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 8);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 9);
lean_inc(x_204);
x_205 = lean_ctor_get(x_193, 10);
lean_inc(x_205);
x_206 = lean_ctor_get(x_193, 11);
lean_inc(x_206);
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
x_208 = lean_ctor_get(x_194, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_194, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_210 = x_194;
} else {
 lean_dec_ref(x_194);
 x_210 = lean_box(0);
}
x_211 = lean_array_get_size(x_209);
x_212 = lean_usize_of_nat(x_211);
lean_dec(x_211);
x_213 = lean_usize_sub(x_212, x_184);
x_214 = lean_usize_land(x_182, x_213);
x_215 = lean_array_uget(x_209, x_214);
x_216 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_add(x_208, x_217);
lean_dec(x_208);
lean_inc(x_190);
x_219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_219, 0, x_1);
lean_ctor_set(x_219, 1, x_190);
lean_ctor_set(x_219, 2, x_215);
x_220 = lean_array_uset(x_209, x_214, x_219);
x_221 = lean_unsigned_to_nat(4u);
x_222 = lean_nat_mul(x_218, x_221);
x_223 = lean_unsigned_to_nat(3u);
x_224 = lean_nat_div(x_222, x_223);
lean_dec(x_222);
x_225 = lean_array_get_size(x_220);
x_226 = lean_nat_dec_le(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Closure_visitLevel___spec__3(x_220);
if (lean_is_scalar(x_210)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_210;
}
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_207)) {
 x_229 = lean_alloc_ctor(0, 12, 0);
} else {
 x_229 = x_207;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_196);
lean_ctor_set(x_229, 2, x_197);
lean_ctor_set(x_229, 3, x_198);
lean_ctor_set(x_229, 4, x_199);
lean_ctor_set(x_229, 5, x_200);
lean_ctor_set(x_229, 6, x_201);
lean_ctor_set(x_229, 7, x_202);
lean_ctor_set(x_229, 8, x_203);
lean_ctor_set(x_229, 9, x_204);
lean_ctor_set(x_229, 10, x_205);
lean_ctor_set(x_229, 11, x_206);
x_230 = lean_st_ref_set(x_3, x_229, x_195);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_190);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
if (lean_is_scalar(x_210)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_210;
}
lean_ctor_set(x_234, 0, x_218);
lean_ctor_set(x_234, 1, x_220);
if (lean_is_scalar(x_207)) {
 x_235 = lean_alloc_ctor(0, 12, 0);
} else {
 x_235 = x_207;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_196);
lean_ctor_set(x_235, 2, x_197);
lean_ctor_set(x_235, 3, x_198);
lean_ctor_set(x_235, 4, x_199);
lean_ctor_set(x_235, 5, x_200);
lean_ctor_set(x_235, 6, x_201);
lean_ctor_set(x_235, 7, x_202);
lean_ctor_set(x_235, 8, x_203);
lean_ctor_set(x_235, 9, x_204);
lean_ctor_set(x_235, 10, x_205);
lean_ctor_set(x_235, 11, x_206);
x_236 = lean_st_ref_set(x_3, x_235, x_195);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_190);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_240 = lean_box(0);
x_241 = lean_array_uset(x_209, x_214, x_240);
lean_inc(x_190);
x_242 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__6(x_1, x_190, x_215);
x_243 = lean_array_uset(x_241, x_214, x_242);
if (lean_is_scalar(x_210)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_210;
}
lean_ctor_set(x_244, 0, x_208);
lean_ctor_set(x_244, 1, x_243);
if (lean_is_scalar(x_207)) {
 x_245 = lean_alloc_ctor(0, 12, 0);
} else {
 x_245 = x_207;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_196);
lean_ctor_set(x_245, 2, x_197);
lean_ctor_set(x_245, 3, x_198);
lean_ctor_set(x_245, 4, x_199);
lean_ctor_set(x_245, 5, x_200);
lean_ctor_set(x_245, 6, x_201);
lean_ctor_set(x_245, 7, x_202);
lean_ctor_set(x_245, 8, x_203);
lean_ctor_set(x_245, 9, x_204);
lean_ctor_set(x_245, 10, x_205);
lean_ctor_set(x_245, 11, x_206);
x_246 = lean_st_ref_set(x_3, x_245, x_195);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_190);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_1);
x_250 = lean_ctor_get(x_188, 0);
lean_inc(x_250);
lean_dec(x_188);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_172);
return x_251;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevel(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_st_ref_get(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVarsCore(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_17);
x_23 = lean_st_ref_set(x_5, x_19, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
x_31 = lean_ctor_get(x_19, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_st_ref_set(x_5, x_32, x_20);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_preprocess___lambda__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_preprocess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 8);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
x_12 = lean_name_append_index_after(x_11, x_10);
x_13 = lean_st_ref_take(x_1, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_14, 8, x_19);
x_20 = lean_st_ref_set(x_1, x_14, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
x_32 = lean_ctor_get(x_14, 7);
x_33 = lean_ctor_get(x_14, 8);
x_34 = lean_ctor_get(x_14, 9);
x_35 = lean_ctor_get(x_14, 10);
x_36 = lean_ctor_get(x_14, 11);
lean_inc(x_36);
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
lean_dec(x_14);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_33, x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_38);
lean_ctor_set(x_39, 9, x_34);
lean_ctor_set(x_39, 10, x_35);
lean_ctor_set(x_39, 11, x_36);
x_40 = lean_st_ref_set(x_1, x_39, x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkNextUserName___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_mkNextUserName(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 11);
x_14 = lean_array_push(x_13, x_1);
lean_ctor_set(x_10, 11, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
x_29 = lean_ctor_get(x_10, 7);
x_30 = lean_ctor_get(x_10, 8);
x_31 = lean_ctor_get(x_10, 9);
x_32 = lean_ctor_get(x_10, 10);
x_33 = lean_ctor_get(x_10, 11);
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
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_34 = lean_array_push(x_33, x_1);
x_35 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_27);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_30);
lean_ctor_set(x_35, 9, x_31);
lean_ctor_set(x_35, 10, x_32);
lean_ctor_set(x_35, 11, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_11);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushToProcess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_6, x_7);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_List_reverse___rarg(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Meta_Closure_collectLevel(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_14;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_8 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_Lean_Meta_Closure_collectLevel(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_2);
x_1 = x_20;
x_2 = x_24;
x_9 = x_23;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mdata expected", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__2;
x_3 = lean_unsigned_to_nat(1706u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__5;
x_3 = lean_unsigned_to_nat(1717u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateApp!Impl", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("application expected", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__8;
x_3 = lean_unsigned_to_nat(1668u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.updateLambdaE!", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lambda expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__11;
x_3 = lean_unsigned_to_nat(1763u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__12;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.updateForallE!", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__14;
x_3 = lean_unsigned_to_nat(1743u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__15;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLet!Impl", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let expression expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__17;
x_3 = lean_unsigned_to_nat(1772u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__18;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_23; lean_object* x_24; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_38);
x_39 = l_Lean_FVarId_getValue_x3f(x_38, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
if (x_2 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_ctor_set(x_41, 1, x_43);
lean_ctor_set(x_41, 0, x_38);
x_45 = l_Lean_Meta_Closure_pushToProcess(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Lean_Expr_fvar___override(x_43);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lean_Expr_fvar___override(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
lean_inc(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Meta_Closure_pushToProcess(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Expr_fvar___override(x_52);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_39, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
lean_dec(x_39);
x_62 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_ctor_set(x_62, 1, x_64);
lean_ctor_set(x_62, 0, x_38);
x_66 = l_Lean_Meta_Closure_pushToProcess(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = l_Lean_Expr_fvar___override(x_64);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = l_Lean_Expr_fvar___override(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
lean_inc(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_38);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Meta_Closure_pushToProcess(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lean_Expr_fvar___override(x_73);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_38);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
lean_dec(x_39);
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
lean_dec(x_60);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_83 = l_Lean_Meta_Closure_preprocess(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_300; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_300 = l_Lean_Expr_hasLevelParam(x_85);
if (x_300 == 0)
{
uint8_t x_301; 
x_301 = l_Lean_Expr_hasFVar(x_85);
if (x_301 == 0)
{
uint8_t x_302; 
x_302 = l_Lean_Expr_hasMVar(x_85);
if (x_302 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_83;
}
else
{
lean_object* x_303; 
lean_free_object(x_83);
x_303 = lean_box(0);
x_87 = x_303;
goto block_299;
}
}
else
{
lean_object* x_304; 
lean_free_object(x_83);
x_304 = lean_box(0);
x_87 = x_304;
goto block_299;
}
}
else
{
lean_object* x_305; 
lean_free_object(x_83);
x_305 = lean_box(0);
x_87 = x_305;
goto block_299;
}
block_299:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_87);
x_88 = lean_st_ref_get(x_3, x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_92 = lean_ctor_get(x_88, 1);
x_93 = lean_ctor_get(x_88, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_array_get_size(x_94);
x_96 = l_Lean_Expr_hash(x_85);
x_97 = 32;
x_98 = lean_uint64_shift_right(x_96, x_97);
x_99 = lean_uint64_xor(x_96, x_98);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_94, x_107);
lean_dec(x_94);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_85, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_free_object(x_88);
lean_inc(x_85);
x_110 = l_Lean_Meta_Closure_collectExprAux(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_92);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_st_ref_take(x_3, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 5);
lean_inc(x_121);
x_122 = lean_ctor_get(x_114, 6);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 7);
lean_inc(x_123);
x_124 = lean_ctor_get(x_114, 8);
lean_inc(x_124);
x_125 = lean_ctor_get(x_114, 9);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 10);
lean_inc(x_126);
x_127 = lean_ctor_get(x_114, 11);
lean_inc(x_127);
lean_dec(x_114);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_115, 0);
x_130 = lean_ctor_get(x_115, 1);
x_131 = lean_array_get_size(x_130);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = lean_usize_sub(x_132, x_105);
x_134 = lean_usize_land(x_103, x_133);
x_135 = lean_array_uget(x_130, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_85, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_129, x_137);
lean_dec(x_129);
lean_inc(x_111);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_85);
lean_ctor_set(x_139, 1, x_111);
lean_ctor_set(x_139, 2, x_135);
x_140 = lean_array_uset(x_130, x_134, x_139);
x_141 = lean_unsigned_to_nat(4u);
x_142 = lean_nat_mul(x_138, x_141);
x_143 = lean_unsigned_to_nat(3u);
x_144 = lean_nat_div(x_142, x_143);
lean_dec(x_142);
x_145 = lean_array_get_size(x_140);
x_146 = lean_nat_dec_le(x_144, x_145);
lean_dec(x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_140);
lean_ctor_set(x_115, 1, x_147);
lean_ctor_set(x_115, 0, x_138);
x_148 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_148, 0, x_117);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set(x_148, 2, x_118);
lean_ctor_set(x_148, 3, x_119);
lean_ctor_set(x_148, 4, x_120);
lean_ctor_set(x_148, 5, x_121);
lean_ctor_set(x_148, 6, x_122);
lean_ctor_set(x_148, 7, x_123);
lean_ctor_set(x_148, 8, x_124);
lean_ctor_set(x_148, 9, x_125);
lean_ctor_set(x_148, 10, x_126);
lean_ctor_set(x_148, 11, x_127);
x_149 = lean_st_ref_set(x_3, x_148, x_116);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_149, 0);
lean_dec(x_151);
lean_ctor_set(x_149, 0, x_111);
return x_149;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_111);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_ctor_set(x_115, 1, x_140);
lean_ctor_set(x_115, 0, x_138);
x_154 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_154, 0, x_117);
lean_ctor_set(x_154, 1, x_115);
lean_ctor_set(x_154, 2, x_118);
lean_ctor_set(x_154, 3, x_119);
lean_ctor_set(x_154, 4, x_120);
lean_ctor_set(x_154, 5, x_121);
lean_ctor_set(x_154, 6, x_122);
lean_ctor_set(x_154, 7, x_123);
lean_ctor_set(x_154, 8, x_124);
lean_ctor_set(x_154, 9, x_125);
lean_ctor_set(x_154, 10, x_126);
lean_ctor_set(x_154, 11, x_127);
x_155 = lean_st_ref_set(x_3, x_154, x_116);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_155, 0);
lean_dec(x_157);
lean_ctor_set(x_155, 0, x_111);
return x_155;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_111);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_160 = lean_box(0);
x_161 = lean_array_uset(x_130, x_134, x_160);
lean_inc(x_111);
x_162 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_85, x_111, x_135);
x_163 = lean_array_uset(x_161, x_134, x_162);
lean_ctor_set(x_115, 1, x_163);
x_164 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_164, 0, x_117);
lean_ctor_set(x_164, 1, x_115);
lean_ctor_set(x_164, 2, x_118);
lean_ctor_set(x_164, 3, x_119);
lean_ctor_set(x_164, 4, x_120);
lean_ctor_set(x_164, 5, x_121);
lean_ctor_set(x_164, 6, x_122);
lean_ctor_set(x_164, 7, x_123);
lean_ctor_set(x_164, 8, x_124);
lean_ctor_set(x_164, 9, x_125);
lean_ctor_set(x_164, 10, x_126);
lean_ctor_set(x_164, 11, x_127);
x_165 = lean_st_ref_set(x_3, x_164, x_116);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 0);
lean_dec(x_167);
lean_ctor_set(x_165, 0, x_111);
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_111);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; size_t x_175; lean_object* x_176; uint8_t x_177; 
x_170 = lean_ctor_get(x_115, 0);
x_171 = lean_ctor_get(x_115, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_115);
x_172 = lean_array_get_size(x_171);
x_173 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_174 = lean_usize_sub(x_173, x_105);
x_175 = lean_usize_land(x_103, x_174);
x_176 = lean_array_uget(x_171, x_175);
x_177 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_85, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_add(x_170, x_178);
lean_dec(x_170);
lean_inc(x_111);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_85);
lean_ctor_set(x_180, 1, x_111);
lean_ctor_set(x_180, 2, x_176);
x_181 = lean_array_uset(x_171, x_175, x_180);
x_182 = lean_unsigned_to_nat(4u);
x_183 = lean_nat_mul(x_179, x_182);
x_184 = lean_unsigned_to_nat(3u);
x_185 = lean_nat_div(x_183, x_184);
lean_dec(x_183);
x_186 = lean_array_get_size(x_181);
x_187 = lean_nat_dec_le(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_181);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_179);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_190, 0, x_117);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_118);
lean_ctor_set(x_190, 3, x_119);
lean_ctor_set(x_190, 4, x_120);
lean_ctor_set(x_190, 5, x_121);
lean_ctor_set(x_190, 6, x_122);
lean_ctor_set(x_190, 7, x_123);
lean_ctor_set(x_190, 8, x_124);
lean_ctor_set(x_190, 9, x_125);
lean_ctor_set(x_190, 10, x_126);
lean_ctor_set(x_190, 11, x_127);
x_191 = lean_st_ref_set(x_3, x_190, x_116);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_111);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_179);
lean_ctor_set(x_195, 1, x_181);
x_196 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_196, 0, x_117);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_118);
lean_ctor_set(x_196, 3, x_119);
lean_ctor_set(x_196, 4, x_120);
lean_ctor_set(x_196, 5, x_121);
lean_ctor_set(x_196, 6, x_122);
lean_ctor_set(x_196, 7, x_123);
lean_ctor_set(x_196, 8, x_124);
lean_ctor_set(x_196, 9, x_125);
lean_ctor_set(x_196, 10, x_126);
lean_ctor_set(x_196, 11, x_127);
x_197 = lean_st_ref_set(x_3, x_196, x_116);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_111);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_201 = lean_box(0);
x_202 = lean_array_uset(x_171, x_175, x_201);
lean_inc(x_111);
x_203 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_85, x_111, x_176);
x_204 = lean_array_uset(x_202, x_175, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_170);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_206, 0, x_117);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_118);
lean_ctor_set(x_206, 3, x_119);
lean_ctor_set(x_206, 4, x_120);
lean_ctor_set(x_206, 5, x_121);
lean_ctor_set(x_206, 6, x_122);
lean_ctor_set(x_206, 7, x_123);
lean_ctor_set(x_206, 8, x_124);
lean_ctor_set(x_206, 9, x_125);
lean_ctor_set(x_206, 10, x_126);
lean_ctor_set(x_206, 11, x_127);
x_207 = lean_st_ref_set(x_3, x_206, x_116);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_111);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_85);
x_211 = !lean_is_exclusive(x_110);
if (x_211 == 0)
{
return x_110;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_110, 0);
x_213 = lean_ctor_get(x_110, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_110);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_215 = lean_ctor_get(x_109, 0);
lean_inc(x_215);
lean_dec(x_109);
lean_ctor_set(x_88, 0, x_215);
return x_88;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; size_t x_226; size_t x_227; size_t x_228; size_t x_229; size_t x_230; lean_object* x_231; lean_object* x_232; 
x_216 = lean_ctor_get(x_88, 1);
lean_inc(x_216);
lean_dec(x_88);
x_217 = lean_ctor_get(x_90, 1);
lean_inc(x_217);
lean_dec(x_90);
x_218 = lean_array_get_size(x_217);
x_219 = l_Lean_Expr_hash(x_85);
x_220 = 32;
x_221 = lean_uint64_shift_right(x_219, x_220);
x_222 = lean_uint64_xor(x_219, x_221);
x_223 = 16;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_xor(x_222, x_224);
x_226 = lean_uint64_to_usize(x_225);
x_227 = lean_usize_of_nat(x_218);
lean_dec(x_218);
x_228 = 1;
x_229 = lean_usize_sub(x_227, x_228);
x_230 = lean_usize_land(x_226, x_229);
x_231 = lean_array_uget(x_217, x_230);
lean_dec(x_217);
x_232 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_85, x_231);
lean_dec(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
lean_inc(x_85);
x_233 = l_Lean_Meta_Closure_collectExprAux(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_216);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; size_t x_255; size_t x_256; size_t x_257; lean_object* x_258; uint8_t x_259; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_st_ref_take(x_3, x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
lean_dec(x_236);
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_237, 4);
lean_inc(x_243);
x_244 = lean_ctor_get(x_237, 5);
lean_inc(x_244);
x_245 = lean_ctor_get(x_237, 6);
lean_inc(x_245);
x_246 = lean_ctor_get(x_237, 7);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 8);
lean_inc(x_247);
x_248 = lean_ctor_get(x_237, 9);
lean_inc(x_248);
x_249 = lean_ctor_get(x_237, 10);
lean_inc(x_249);
x_250 = lean_ctor_get(x_237, 11);
lean_inc(x_250);
lean_dec(x_237);
x_251 = lean_ctor_get(x_238, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_238, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_253 = x_238;
} else {
 lean_dec_ref(x_238);
 x_253 = lean_box(0);
}
x_254 = lean_array_get_size(x_252);
x_255 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_256 = lean_usize_sub(x_255, x_228);
x_257 = lean_usize_land(x_226, x_256);
x_258 = lean_array_uget(x_252, x_257);
x_259 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_85, x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_add(x_251, x_260);
lean_dec(x_251);
lean_inc(x_234);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_85);
lean_ctor_set(x_262, 1, x_234);
lean_ctor_set(x_262, 2, x_258);
x_263 = lean_array_uset(x_252, x_257, x_262);
x_264 = lean_unsigned_to_nat(4u);
x_265 = lean_nat_mul(x_261, x_264);
x_266 = lean_unsigned_to_nat(3u);
x_267 = lean_nat_div(x_265, x_266);
lean_dec(x_265);
x_268 = lean_array_get_size(x_263);
x_269 = lean_nat_dec_le(x_267, x_268);
lean_dec(x_268);
lean_dec(x_267);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_263);
if (lean_is_scalar(x_253)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_253;
}
lean_ctor_set(x_271, 0, x_261);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_272, 0, x_240);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set(x_272, 2, x_241);
lean_ctor_set(x_272, 3, x_242);
lean_ctor_set(x_272, 4, x_243);
lean_ctor_set(x_272, 5, x_244);
lean_ctor_set(x_272, 6, x_245);
lean_ctor_set(x_272, 7, x_246);
lean_ctor_set(x_272, 8, x_247);
lean_ctor_set(x_272, 9, x_248);
lean_ctor_set(x_272, 10, x_249);
lean_ctor_set(x_272, 11, x_250);
x_273 = lean_st_ref_set(x_3, x_272, x_239);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_234);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
if (lean_is_scalar(x_253)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_253;
}
lean_ctor_set(x_277, 0, x_261);
lean_ctor_set(x_277, 1, x_263);
x_278 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_278, 0, x_240);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_241);
lean_ctor_set(x_278, 3, x_242);
lean_ctor_set(x_278, 4, x_243);
lean_ctor_set(x_278, 5, x_244);
lean_ctor_set(x_278, 6, x_245);
lean_ctor_set(x_278, 7, x_246);
lean_ctor_set(x_278, 8, x_247);
lean_ctor_set(x_278, 9, x_248);
lean_ctor_set(x_278, 10, x_249);
lean_ctor_set(x_278, 11, x_250);
x_279 = lean_st_ref_set(x_3, x_278, x_239);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_281 = x_279;
} else {
 lean_dec_ref(x_279);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_234);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_283 = lean_box(0);
x_284 = lean_array_uset(x_252, x_257, x_283);
lean_inc(x_234);
x_285 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_85, x_234, x_258);
x_286 = lean_array_uset(x_284, x_257, x_285);
if (lean_is_scalar(x_253)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_253;
}
lean_ctor_set(x_287, 0, x_251);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_288, 0, x_240);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_241);
lean_ctor_set(x_288, 3, x_242);
lean_ctor_set(x_288, 4, x_243);
lean_ctor_set(x_288, 5, x_244);
lean_ctor_set(x_288, 6, x_245);
lean_ctor_set(x_288, 7, x_246);
lean_ctor_set(x_288, 8, x_247);
lean_ctor_set(x_288, 9, x_248);
lean_ctor_set(x_288, 10, x_249);
lean_ctor_set(x_288, 11, x_250);
x_289 = lean_st_ref_set(x_3, x_288, x_239);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_234);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_85);
x_293 = lean_ctor_get(x_233, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_233, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_295 = x_233;
} else {
 lean_dec_ref(x_233);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_297 = lean_ctor_get(x_232, 0);
lean_inc(x_297);
lean_dec(x_232);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_216);
return x_298;
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_397; 
x_306 = lean_ctor_get(x_83, 0);
x_307 = lean_ctor_get(x_83, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_83);
x_397 = l_Lean_Expr_hasLevelParam(x_306);
if (x_397 == 0)
{
uint8_t x_398; 
x_398 = l_Lean_Expr_hasFVar(x_306);
if (x_398 == 0)
{
uint8_t x_399; 
x_399 = l_Lean_Expr_hasMVar(x_306);
if (x_399 == 0)
{
lean_object* x_400; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_306);
lean_ctor_set(x_400, 1, x_307);
return x_400;
}
else
{
lean_object* x_401; 
x_401 = lean_box(0);
x_308 = x_401;
goto block_396;
}
}
else
{
lean_object* x_402; 
x_402 = lean_box(0);
x_308 = x_402;
goto block_396;
}
}
else
{
lean_object* x_403; 
x_403 = lean_box(0);
x_308 = x_403;
goto block_396;
}
block_396:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint64_t x_316; uint64_t x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; size_t x_323; size_t x_324; size_t x_325; size_t x_326; size_t x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_308);
x_309 = lean_st_ref_get(x_3, x_307);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_313 = x_309;
} else {
 lean_dec_ref(x_309);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_array_get_size(x_314);
x_316 = l_Lean_Expr_hash(x_306);
x_317 = 32;
x_318 = lean_uint64_shift_right(x_316, x_317);
x_319 = lean_uint64_xor(x_316, x_318);
x_320 = 16;
x_321 = lean_uint64_shift_right(x_319, x_320);
x_322 = lean_uint64_xor(x_319, x_321);
x_323 = lean_uint64_to_usize(x_322);
x_324 = lean_usize_of_nat(x_315);
lean_dec(x_315);
x_325 = 1;
x_326 = lean_usize_sub(x_324, x_325);
x_327 = lean_usize_land(x_323, x_326);
x_328 = lean_array_uget(x_314, x_327);
lean_dec(x_314);
x_329 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_306, x_328);
lean_dec(x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; 
lean_dec(x_313);
lean_inc(x_306);
x_330 = l_Lean_Meta_Closure_collectExprAux(x_306, x_2, x_3, x_4, x_5, x_6, x_7, x_312);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; size_t x_352; size_t x_353; size_t x_354; lean_object* x_355; uint8_t x_356; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_st_ref_take(x_3, x_332);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_ctor_get(x_334, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_334, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_334, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_334, 5);
lean_inc(x_341);
x_342 = lean_ctor_get(x_334, 6);
lean_inc(x_342);
x_343 = lean_ctor_get(x_334, 7);
lean_inc(x_343);
x_344 = lean_ctor_get(x_334, 8);
lean_inc(x_344);
x_345 = lean_ctor_get(x_334, 9);
lean_inc(x_345);
x_346 = lean_ctor_get(x_334, 10);
lean_inc(x_346);
x_347 = lean_ctor_get(x_334, 11);
lean_inc(x_347);
lean_dec(x_334);
x_348 = lean_ctor_get(x_335, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_335, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_350 = x_335;
} else {
 lean_dec_ref(x_335);
 x_350 = lean_box(0);
}
x_351 = lean_array_get_size(x_349);
x_352 = lean_usize_of_nat(x_351);
lean_dec(x_351);
x_353 = lean_usize_sub(x_352, x_325);
x_354 = lean_usize_land(x_323, x_353);
x_355 = lean_array_uget(x_349, x_354);
x_356 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_306, x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_nat_add(x_348, x_357);
lean_dec(x_348);
lean_inc(x_331);
x_359 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_359, 0, x_306);
lean_ctor_set(x_359, 1, x_331);
lean_ctor_set(x_359, 2, x_355);
x_360 = lean_array_uset(x_349, x_354, x_359);
x_361 = lean_unsigned_to_nat(4u);
x_362 = lean_nat_mul(x_358, x_361);
x_363 = lean_unsigned_to_nat(3u);
x_364 = lean_nat_div(x_362, x_363);
lean_dec(x_362);
x_365 = lean_array_get_size(x_360);
x_366 = lean_nat_dec_le(x_364, x_365);
lean_dec(x_365);
lean_dec(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_367 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_360);
if (lean_is_scalar(x_350)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_350;
}
lean_ctor_set(x_368, 0, x_358);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_369, 0, x_337);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_338);
lean_ctor_set(x_369, 3, x_339);
lean_ctor_set(x_369, 4, x_340);
lean_ctor_set(x_369, 5, x_341);
lean_ctor_set(x_369, 6, x_342);
lean_ctor_set(x_369, 7, x_343);
lean_ctor_set(x_369, 8, x_344);
lean_ctor_set(x_369, 9, x_345);
lean_ctor_set(x_369, 10, x_346);
lean_ctor_set(x_369, 11, x_347);
x_370 = lean_st_ref_set(x_3, x_369, x_336);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_372 = x_370;
} else {
 lean_dec_ref(x_370);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_331);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
if (lean_is_scalar(x_350)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_350;
}
lean_ctor_set(x_374, 0, x_358);
lean_ctor_set(x_374, 1, x_360);
x_375 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_375, 0, x_337);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_375, 2, x_338);
lean_ctor_set(x_375, 3, x_339);
lean_ctor_set(x_375, 4, x_340);
lean_ctor_set(x_375, 5, x_341);
lean_ctor_set(x_375, 6, x_342);
lean_ctor_set(x_375, 7, x_343);
lean_ctor_set(x_375, 8, x_344);
lean_ctor_set(x_375, 9, x_345);
lean_ctor_set(x_375, 10, x_346);
lean_ctor_set(x_375, 11, x_347);
x_376 = lean_st_ref_set(x_3, x_375, x_336);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_331);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_380 = lean_box(0);
x_381 = lean_array_uset(x_349, x_354, x_380);
lean_inc(x_331);
x_382 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_306, x_331, x_355);
x_383 = lean_array_uset(x_381, x_354, x_382);
if (lean_is_scalar(x_350)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_350;
}
lean_ctor_set(x_384, 0, x_348);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_385, 0, x_337);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set(x_385, 2, x_338);
lean_ctor_set(x_385, 3, x_339);
lean_ctor_set(x_385, 4, x_340);
lean_ctor_set(x_385, 5, x_341);
lean_ctor_set(x_385, 6, x_342);
lean_ctor_set(x_385, 7, x_343);
lean_ctor_set(x_385, 8, x_344);
lean_ctor_set(x_385, 9, x_345);
lean_ctor_set(x_385, 10, x_346);
lean_ctor_set(x_385, 11, x_347);
x_386 = lean_st_ref_set(x_3, x_385, x_336);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_388 = x_386;
} else {
 lean_dec_ref(x_386);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_331);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_306);
x_390 = lean_ctor_get(x_330, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_330, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_392 = x_330;
} else {
 lean_dec_ref(x_330);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_306);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_394 = lean_ctor_get(x_329, 0);
lean_inc(x_394);
lean_dec(x_329);
if (lean_is_scalar(x_313)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_313;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_312);
return x_395;
}
}
}
}
else
{
uint8_t x_404; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_404 = !lean_is_exclusive(x_83);
if (x_404 == 0)
{
return x_83;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_83, 0);
x_406 = lean_ctor_get(x_83, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_83);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_408 = !lean_is_exclusive(x_39);
if (x_408 == 0)
{
return x_39;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_39, 0);
x_410 = lean_ctor_get(x_39, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_39);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
case 2:
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_1, 0);
lean_inc(x_412);
x_413 = l_Lean_MVarId_getDecl(x_412, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 2);
lean_inc(x_416);
lean_dec(x_414);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_417 = l_Lean_Meta_Closure_preprocess(x_416, x_2, x_3, x_4, x_5, x_6, x_7, x_415);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_458; uint8_t x_571; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_571 = l_Lean_Expr_hasLevelParam(x_418);
if (x_571 == 0)
{
uint8_t x_572; 
x_572 = l_Lean_Expr_hasFVar(x_418);
if (x_572 == 0)
{
uint8_t x_573; 
x_573 = l_Lean_Expr_hasMVar(x_418);
if (x_573 == 0)
{
x_420 = x_418;
x_421 = x_419;
goto block_457;
}
else
{
lean_object* x_574; 
x_574 = lean_box(0);
x_458 = x_574;
goto block_570;
}
}
else
{
lean_object* x_575; 
x_575 = lean_box(0);
x_458 = x_575;
goto block_570;
}
}
else
{
lean_object* x_576; 
x_576 = lean_box(0);
x_458 = x_576;
goto block_570;
}
block_457:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_422 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_421);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_424);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = lean_st_ref_take(x_3, x_427);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_429, 2);
lean_inc(x_433);
x_434 = lean_ctor_get(x_429, 3);
lean_inc(x_434);
x_435 = lean_ctor_get(x_429, 4);
lean_inc(x_435);
x_436 = lean_ctor_get(x_429, 5);
lean_inc(x_436);
x_437 = lean_ctor_get(x_429, 6);
lean_inc(x_437);
x_438 = lean_unsigned_to_nat(0u);
x_439 = 0;
x_440 = 0;
lean_inc(x_423);
x_441 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_423);
lean_ctor_set(x_441, 2, x_426);
lean_ctor_set(x_441, 3, x_420);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_439);
lean_ctor_set_uint8(x_441, sizeof(void*)*4 + 1, x_440);
x_442 = lean_array_push(x_437, x_441);
x_443 = lean_ctor_get(x_429, 7);
lean_inc(x_443);
x_444 = lean_ctor_get(x_429, 8);
lean_inc(x_444);
x_445 = lean_ctor_get(x_429, 9);
lean_inc(x_445);
x_446 = lean_array_push(x_445, x_1);
x_447 = lean_ctor_get(x_429, 10);
lean_inc(x_447);
x_448 = lean_ctor_get(x_429, 11);
lean_inc(x_448);
lean_dec(x_429);
x_449 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_449, 0, x_431);
lean_ctor_set(x_449, 1, x_432);
lean_ctor_set(x_449, 2, x_433);
lean_ctor_set(x_449, 3, x_434);
lean_ctor_set(x_449, 4, x_435);
lean_ctor_set(x_449, 5, x_436);
lean_ctor_set(x_449, 6, x_442);
lean_ctor_set(x_449, 7, x_443);
lean_ctor_set(x_449, 8, x_444);
lean_ctor_set(x_449, 9, x_446);
lean_ctor_set(x_449, 10, x_447);
lean_ctor_set(x_449, 11, x_448);
x_450 = lean_st_ref_set(x_3, x_449, x_430);
x_451 = !lean_is_exclusive(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_450, 0);
lean_dec(x_452);
x_453 = l_Lean_Expr_fvar___override(x_423);
lean_ctor_set(x_450, 0, x_453);
return x_450;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_450, 1);
lean_inc(x_454);
lean_dec(x_450);
x_455 = l_Lean_Expr_fvar___override(x_423);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
block_570:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint64_t x_465; uint64_t x_466; uint64_t x_467; uint64_t x_468; uint64_t x_469; uint64_t x_470; uint64_t x_471; size_t x_472; size_t x_473; size_t x_474; size_t x_475; size_t x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_458);
x_459 = lean_st_ref_get(x_3, x_419);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_array_get_size(x_463);
x_465 = l_Lean_Expr_hash(x_418);
x_466 = 32;
x_467 = lean_uint64_shift_right(x_465, x_466);
x_468 = lean_uint64_xor(x_465, x_467);
x_469 = 16;
x_470 = lean_uint64_shift_right(x_468, x_469);
x_471 = lean_uint64_xor(x_468, x_470);
x_472 = lean_uint64_to_usize(x_471);
x_473 = lean_usize_of_nat(x_464);
lean_dec(x_464);
x_474 = 1;
x_475 = lean_usize_sub(x_473, x_474);
x_476 = lean_usize_land(x_472, x_475);
x_477 = lean_array_uget(x_463, x_476);
lean_dec(x_463);
x_478 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_418, x_477);
lean_dec(x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_418);
x_479 = l_Lean_Meta_Closure_collectExprAux(x_418, x_2, x_3, x_4, x_5, x_6, x_7, x_462);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_st_ref_take(x_3, x_481);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
x_486 = lean_ctor_get(x_483, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_483, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_483, 3);
lean_inc(x_488);
x_489 = lean_ctor_get(x_483, 4);
lean_inc(x_489);
x_490 = lean_ctor_get(x_483, 5);
lean_inc(x_490);
x_491 = lean_ctor_get(x_483, 6);
lean_inc(x_491);
x_492 = lean_ctor_get(x_483, 7);
lean_inc(x_492);
x_493 = lean_ctor_get(x_483, 8);
lean_inc(x_493);
x_494 = lean_ctor_get(x_483, 9);
lean_inc(x_494);
x_495 = lean_ctor_get(x_483, 10);
lean_inc(x_495);
x_496 = lean_ctor_get(x_483, 11);
lean_inc(x_496);
lean_dec(x_483);
x_497 = !lean_is_exclusive(x_484);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; size_t x_501; size_t x_502; size_t x_503; lean_object* x_504; uint8_t x_505; 
x_498 = lean_ctor_get(x_484, 0);
x_499 = lean_ctor_get(x_484, 1);
x_500 = lean_array_get_size(x_499);
x_501 = lean_usize_of_nat(x_500);
lean_dec(x_500);
x_502 = lean_usize_sub(x_501, x_474);
x_503 = lean_usize_land(x_472, x_502);
x_504 = lean_array_uget(x_499, x_503);
x_505 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_418, x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_506 = lean_unsigned_to_nat(1u);
x_507 = lean_nat_add(x_498, x_506);
lean_dec(x_498);
lean_inc(x_480);
x_508 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_508, 0, x_418);
lean_ctor_set(x_508, 1, x_480);
lean_ctor_set(x_508, 2, x_504);
x_509 = lean_array_uset(x_499, x_503, x_508);
x_510 = lean_unsigned_to_nat(4u);
x_511 = lean_nat_mul(x_507, x_510);
x_512 = lean_unsigned_to_nat(3u);
x_513 = lean_nat_div(x_511, x_512);
lean_dec(x_511);
x_514 = lean_array_get_size(x_509);
x_515 = lean_nat_dec_le(x_513, x_514);
lean_dec(x_514);
lean_dec(x_513);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_509);
lean_ctor_set(x_484, 1, x_516);
lean_ctor_set(x_484, 0, x_507);
x_517 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_517, 0, x_486);
lean_ctor_set(x_517, 1, x_484);
lean_ctor_set(x_517, 2, x_487);
lean_ctor_set(x_517, 3, x_488);
lean_ctor_set(x_517, 4, x_489);
lean_ctor_set(x_517, 5, x_490);
lean_ctor_set(x_517, 6, x_491);
lean_ctor_set(x_517, 7, x_492);
lean_ctor_set(x_517, 8, x_493);
lean_ctor_set(x_517, 9, x_494);
lean_ctor_set(x_517, 10, x_495);
lean_ctor_set(x_517, 11, x_496);
x_518 = lean_st_ref_set(x_3, x_517, x_485);
x_519 = lean_ctor_get(x_518, 1);
lean_inc(x_519);
lean_dec(x_518);
x_420 = x_480;
x_421 = x_519;
goto block_457;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_ctor_set(x_484, 1, x_509);
lean_ctor_set(x_484, 0, x_507);
x_520 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_520, 0, x_486);
lean_ctor_set(x_520, 1, x_484);
lean_ctor_set(x_520, 2, x_487);
lean_ctor_set(x_520, 3, x_488);
lean_ctor_set(x_520, 4, x_489);
lean_ctor_set(x_520, 5, x_490);
lean_ctor_set(x_520, 6, x_491);
lean_ctor_set(x_520, 7, x_492);
lean_ctor_set(x_520, 8, x_493);
lean_ctor_set(x_520, 9, x_494);
lean_ctor_set(x_520, 10, x_495);
lean_ctor_set(x_520, 11, x_496);
x_521 = lean_st_ref_set(x_3, x_520, x_485);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_420 = x_480;
x_421 = x_522;
goto block_457;
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_523 = lean_box(0);
x_524 = lean_array_uset(x_499, x_503, x_523);
lean_inc(x_480);
x_525 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_418, x_480, x_504);
x_526 = lean_array_uset(x_524, x_503, x_525);
lean_ctor_set(x_484, 1, x_526);
x_527 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_527, 0, x_486);
lean_ctor_set(x_527, 1, x_484);
lean_ctor_set(x_527, 2, x_487);
lean_ctor_set(x_527, 3, x_488);
lean_ctor_set(x_527, 4, x_489);
lean_ctor_set(x_527, 5, x_490);
lean_ctor_set(x_527, 6, x_491);
lean_ctor_set(x_527, 7, x_492);
lean_ctor_set(x_527, 8, x_493);
lean_ctor_set(x_527, 9, x_494);
lean_ctor_set(x_527, 10, x_495);
lean_ctor_set(x_527, 11, x_496);
x_528 = lean_st_ref_set(x_3, x_527, x_485);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
lean_dec(x_528);
x_420 = x_480;
x_421 = x_529;
goto block_457;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; size_t x_533; size_t x_534; size_t x_535; lean_object* x_536; uint8_t x_537; 
x_530 = lean_ctor_get(x_484, 0);
x_531 = lean_ctor_get(x_484, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_484);
x_532 = lean_array_get_size(x_531);
x_533 = lean_usize_of_nat(x_532);
lean_dec(x_532);
x_534 = lean_usize_sub(x_533, x_474);
x_535 = lean_usize_land(x_472, x_534);
x_536 = lean_array_uget(x_531, x_535);
x_537 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_418, x_536);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; 
x_538 = lean_unsigned_to_nat(1u);
x_539 = lean_nat_add(x_530, x_538);
lean_dec(x_530);
lean_inc(x_480);
x_540 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_540, 0, x_418);
lean_ctor_set(x_540, 1, x_480);
lean_ctor_set(x_540, 2, x_536);
x_541 = lean_array_uset(x_531, x_535, x_540);
x_542 = lean_unsigned_to_nat(4u);
x_543 = lean_nat_mul(x_539, x_542);
x_544 = lean_unsigned_to_nat(3u);
x_545 = lean_nat_div(x_543, x_544);
lean_dec(x_543);
x_546 = lean_array_get_size(x_541);
x_547 = lean_nat_dec_le(x_545, x_546);
lean_dec(x_546);
lean_dec(x_545);
if (x_547 == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_548 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_541);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_539);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_550, 0, x_486);
lean_ctor_set(x_550, 1, x_549);
lean_ctor_set(x_550, 2, x_487);
lean_ctor_set(x_550, 3, x_488);
lean_ctor_set(x_550, 4, x_489);
lean_ctor_set(x_550, 5, x_490);
lean_ctor_set(x_550, 6, x_491);
lean_ctor_set(x_550, 7, x_492);
lean_ctor_set(x_550, 8, x_493);
lean_ctor_set(x_550, 9, x_494);
lean_ctor_set(x_550, 10, x_495);
lean_ctor_set(x_550, 11, x_496);
x_551 = lean_st_ref_set(x_3, x_550, x_485);
x_552 = lean_ctor_get(x_551, 1);
lean_inc(x_552);
lean_dec(x_551);
x_420 = x_480;
x_421 = x_552;
goto block_457;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_539);
lean_ctor_set(x_553, 1, x_541);
x_554 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_554, 0, x_486);
lean_ctor_set(x_554, 1, x_553);
lean_ctor_set(x_554, 2, x_487);
lean_ctor_set(x_554, 3, x_488);
lean_ctor_set(x_554, 4, x_489);
lean_ctor_set(x_554, 5, x_490);
lean_ctor_set(x_554, 6, x_491);
lean_ctor_set(x_554, 7, x_492);
lean_ctor_set(x_554, 8, x_493);
lean_ctor_set(x_554, 9, x_494);
lean_ctor_set(x_554, 10, x_495);
lean_ctor_set(x_554, 11, x_496);
x_555 = lean_st_ref_set(x_3, x_554, x_485);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec(x_555);
x_420 = x_480;
x_421 = x_556;
goto block_457;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_557 = lean_box(0);
x_558 = lean_array_uset(x_531, x_535, x_557);
lean_inc(x_480);
x_559 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_418, x_480, x_536);
x_560 = lean_array_uset(x_558, x_535, x_559);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_530);
lean_ctor_set(x_561, 1, x_560);
x_562 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_562, 0, x_486);
lean_ctor_set(x_562, 1, x_561);
lean_ctor_set(x_562, 2, x_487);
lean_ctor_set(x_562, 3, x_488);
lean_ctor_set(x_562, 4, x_489);
lean_ctor_set(x_562, 5, x_490);
lean_ctor_set(x_562, 6, x_491);
lean_ctor_set(x_562, 7, x_492);
lean_ctor_set(x_562, 8, x_493);
lean_ctor_set(x_562, 9, x_494);
lean_ctor_set(x_562, 10, x_495);
lean_ctor_set(x_562, 11, x_496);
x_563 = lean_st_ref_set(x_3, x_562, x_485);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
lean_dec(x_563);
x_420 = x_480;
x_421 = x_564;
goto block_457;
}
}
}
else
{
uint8_t x_565; 
lean_dec(x_418);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_565 = !lean_is_exclusive(x_479);
if (x_565 == 0)
{
return x_479;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_479, 0);
x_567 = lean_ctor_get(x_479, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_479);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_567);
return x_568;
}
}
}
else
{
lean_object* x_569; 
lean_dec(x_418);
x_569 = lean_ctor_get(x_478, 0);
lean_inc(x_569);
lean_dec(x_478);
x_420 = x_569;
x_421 = x_462;
goto block_457;
}
}
}
else
{
uint8_t x_577; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_577 = !lean_is_exclusive(x_417);
if (x_577 == 0)
{
return x_417;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_417, 0);
x_579 = lean_ctor_get(x_417, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_417);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
}
else
{
uint8_t x_581; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_581 = !lean_is_exclusive(x_413);
if (x_581 == 0)
{
return x_413;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_413, 0);
x_583 = lean_ctor_get(x_413, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_413);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
case 3:
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = lean_ctor_get(x_1, 0);
lean_inc(x_585);
lean_inc(x_585);
x_586 = l_Lean_Meta_Closure_collectLevel(x_585, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_587 = !lean_is_exclusive(x_586);
if (x_587 == 0)
{
lean_object* x_588; size_t x_589; size_t x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
x_589 = lean_ptr_addr(x_585);
lean_dec(x_585);
x_590 = lean_ptr_addr(x_588);
x_591 = lean_usize_dec_eq(x_589, x_590);
if (x_591 == 0)
{
lean_object* x_592; 
lean_dec(x_1);
x_592 = l_Lean_Expr_sort___override(x_588);
lean_ctor_set(x_586, 0, x_592);
return x_586;
}
else
{
lean_dec(x_588);
lean_ctor_set(x_586, 0, x_1);
return x_586;
}
}
else
{
lean_object* x_593; lean_object* x_594; size_t x_595; size_t x_596; uint8_t x_597; 
x_593 = lean_ctor_get(x_586, 0);
x_594 = lean_ctor_get(x_586, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_586);
x_595 = lean_ptr_addr(x_585);
lean_dec(x_585);
x_596 = lean_ptr_addr(x_593);
x_597 = lean_usize_dec_eq(x_595, x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; 
lean_dec(x_1);
x_598 = l_Lean_Expr_sort___override(x_593);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_594);
return x_599;
}
else
{
lean_object* x_600; 
lean_dec(x_593);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_1);
lean_ctor_set(x_600, 1, x_594);
return x_600;
}
}
}
case 4:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
x_601 = lean_ctor_get(x_1, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_1, 1);
lean_inc(x_602);
x_603 = lean_box(0);
lean_inc(x_602);
x_604 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_602, x_603, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_605 = !lean_is_exclusive(x_604);
if (x_605 == 0)
{
lean_object* x_606; uint8_t x_607; 
x_606 = lean_ctor_get(x_604, 0);
x_607 = l_ptrEqList___rarg(x_602, x_606);
lean_dec(x_602);
if (x_607 == 0)
{
lean_object* x_608; 
lean_dec(x_1);
x_608 = l_Lean_Expr_const___override(x_601, x_606);
lean_ctor_set(x_604, 0, x_608);
return x_604;
}
else
{
lean_dec(x_606);
lean_dec(x_601);
lean_ctor_set(x_604, 0, x_1);
return x_604;
}
}
else
{
lean_object* x_609; lean_object* x_610; uint8_t x_611; 
x_609 = lean_ctor_get(x_604, 0);
x_610 = lean_ctor_get(x_604, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_604);
x_611 = l_ptrEqList___rarg(x_602, x_609);
lean_dec(x_602);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_1);
x_612 = l_Lean_Expr_const___override(x_601, x_609);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_610);
return x_613;
}
else
{
lean_object* x_614; 
lean_dec(x_609);
lean_dec(x_601);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_1);
lean_ctor_set(x_614, 1, x_610);
return x_614;
}
}
}
case 5:
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_758; uint8_t x_871; 
x_615 = lean_ctor_get(x_1, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_1, 1);
lean_inc(x_616);
x_871 = l_Lean_Expr_hasLevelParam(x_615);
if (x_871 == 0)
{
uint8_t x_872; 
x_872 = l_Lean_Expr_hasFVar(x_615);
if (x_872 == 0)
{
uint8_t x_873; 
x_873 = l_Lean_Expr_hasMVar(x_615);
if (x_873 == 0)
{
x_617 = x_615;
x_618 = x_8;
goto block_757;
}
else
{
lean_object* x_874; 
x_874 = lean_box(0);
x_758 = x_874;
goto block_870;
}
}
else
{
lean_object* x_875; 
x_875 = lean_box(0);
x_758 = x_875;
goto block_870;
}
}
else
{
lean_object* x_876; 
x_876 = lean_box(0);
x_758 = x_876;
goto block_870;
}
block_757:
{
lean_object* x_619; lean_object* x_620; lean_object* x_638; uint8_t x_751; 
x_751 = l_Lean_Expr_hasLevelParam(x_616);
if (x_751 == 0)
{
uint8_t x_752; 
x_752 = l_Lean_Expr_hasFVar(x_616);
if (x_752 == 0)
{
uint8_t x_753; 
x_753 = l_Lean_Expr_hasMVar(x_616);
if (x_753 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_619 = x_616;
x_620 = x_618;
goto block_637;
}
else
{
lean_object* x_754; 
x_754 = lean_box(0);
x_638 = x_754;
goto block_750;
}
}
else
{
lean_object* x_755; 
x_755 = lean_box(0);
x_638 = x_755;
goto block_750;
}
}
else
{
lean_object* x_756; 
x_756 = lean_box(0);
x_638 = x_756;
goto block_750;
}
block_637:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_621; lean_object* x_622; size_t x_623; size_t x_624; uint8_t x_625; 
x_621 = lean_ctor_get(x_1, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_1, 1);
lean_inc(x_622);
x_623 = lean_ptr_addr(x_621);
lean_dec(x_621);
x_624 = lean_ptr_addr(x_617);
x_625 = lean_usize_dec_eq(x_623, x_624);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
lean_dec(x_622);
lean_dec(x_1);
x_626 = l_Lean_Expr_app___override(x_617, x_619);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_620);
return x_627;
}
else
{
size_t x_628; size_t x_629; uint8_t x_630; 
x_628 = lean_ptr_addr(x_622);
lean_dec(x_622);
x_629 = lean_ptr_addr(x_619);
x_630 = lean_usize_dec_eq(x_628, x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
lean_dec(x_1);
x_631 = l_Lean_Expr_app___override(x_617, x_619);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_620);
return x_632;
}
else
{
lean_object* x_633; 
lean_dec(x_619);
lean_dec(x_617);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_1);
lean_ctor_set(x_633, 1, x_620);
return x_633;
}
}
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_619);
lean_dec(x_617);
lean_dec(x_1);
x_634 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_635 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_634);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_620);
return x_636;
}
}
block_750:
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint64_t x_645; uint64_t x_646; uint64_t x_647; uint64_t x_648; uint64_t x_649; uint64_t x_650; uint64_t x_651; size_t x_652; size_t x_653; size_t x_654; size_t x_655; size_t x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_638);
x_639 = lean_st_ref_get(x_3, x_618);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
lean_dec(x_640);
x_642 = lean_ctor_get(x_639, 1);
lean_inc(x_642);
lean_dec(x_639);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = lean_array_get_size(x_643);
x_645 = l_Lean_Expr_hash(x_616);
x_646 = 32;
x_647 = lean_uint64_shift_right(x_645, x_646);
x_648 = lean_uint64_xor(x_645, x_647);
x_649 = 16;
x_650 = lean_uint64_shift_right(x_648, x_649);
x_651 = lean_uint64_xor(x_648, x_650);
x_652 = lean_uint64_to_usize(x_651);
x_653 = lean_usize_of_nat(x_644);
lean_dec(x_644);
x_654 = 1;
x_655 = lean_usize_sub(x_653, x_654);
x_656 = lean_usize_land(x_652, x_655);
x_657 = lean_array_uget(x_643, x_656);
lean_dec(x_643);
x_658 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_616, x_657);
lean_dec(x_657);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; 
lean_inc(x_616);
x_659 = l_Lean_Meta_Closure_collectExprAux(x_616, x_2, x_3, x_4, x_5, x_6, x_7, x_642);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_662 = lean_st_ref_take(x_3, x_661);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_662, 1);
lean_inc(x_665);
lean_dec(x_662);
x_666 = lean_ctor_get(x_663, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_663, 2);
lean_inc(x_667);
x_668 = lean_ctor_get(x_663, 3);
lean_inc(x_668);
x_669 = lean_ctor_get(x_663, 4);
lean_inc(x_669);
x_670 = lean_ctor_get(x_663, 5);
lean_inc(x_670);
x_671 = lean_ctor_get(x_663, 6);
lean_inc(x_671);
x_672 = lean_ctor_get(x_663, 7);
lean_inc(x_672);
x_673 = lean_ctor_get(x_663, 8);
lean_inc(x_673);
x_674 = lean_ctor_get(x_663, 9);
lean_inc(x_674);
x_675 = lean_ctor_get(x_663, 10);
lean_inc(x_675);
x_676 = lean_ctor_get(x_663, 11);
lean_inc(x_676);
lean_dec(x_663);
x_677 = !lean_is_exclusive(x_664);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; size_t x_681; size_t x_682; size_t x_683; lean_object* x_684; uint8_t x_685; 
x_678 = lean_ctor_get(x_664, 0);
x_679 = lean_ctor_get(x_664, 1);
x_680 = lean_array_get_size(x_679);
x_681 = lean_usize_of_nat(x_680);
lean_dec(x_680);
x_682 = lean_usize_sub(x_681, x_654);
x_683 = lean_usize_land(x_652, x_682);
x_684 = lean_array_uget(x_679, x_683);
x_685 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_616, x_684);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
x_686 = lean_unsigned_to_nat(1u);
x_687 = lean_nat_add(x_678, x_686);
lean_dec(x_678);
lean_inc(x_660);
x_688 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_688, 0, x_616);
lean_ctor_set(x_688, 1, x_660);
lean_ctor_set(x_688, 2, x_684);
x_689 = lean_array_uset(x_679, x_683, x_688);
x_690 = lean_unsigned_to_nat(4u);
x_691 = lean_nat_mul(x_687, x_690);
x_692 = lean_unsigned_to_nat(3u);
x_693 = lean_nat_div(x_691, x_692);
lean_dec(x_691);
x_694 = lean_array_get_size(x_689);
x_695 = lean_nat_dec_le(x_693, x_694);
lean_dec(x_694);
lean_dec(x_693);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_696 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_689);
lean_ctor_set(x_664, 1, x_696);
lean_ctor_set(x_664, 0, x_687);
x_697 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_697, 0, x_666);
lean_ctor_set(x_697, 1, x_664);
lean_ctor_set(x_697, 2, x_667);
lean_ctor_set(x_697, 3, x_668);
lean_ctor_set(x_697, 4, x_669);
lean_ctor_set(x_697, 5, x_670);
lean_ctor_set(x_697, 6, x_671);
lean_ctor_set(x_697, 7, x_672);
lean_ctor_set(x_697, 8, x_673);
lean_ctor_set(x_697, 9, x_674);
lean_ctor_set(x_697, 10, x_675);
lean_ctor_set(x_697, 11, x_676);
x_698 = lean_st_ref_set(x_3, x_697, x_665);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
lean_dec(x_698);
x_619 = x_660;
x_620 = x_699;
goto block_637;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_ctor_set(x_664, 1, x_689);
lean_ctor_set(x_664, 0, x_687);
x_700 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_700, 0, x_666);
lean_ctor_set(x_700, 1, x_664);
lean_ctor_set(x_700, 2, x_667);
lean_ctor_set(x_700, 3, x_668);
lean_ctor_set(x_700, 4, x_669);
lean_ctor_set(x_700, 5, x_670);
lean_ctor_set(x_700, 6, x_671);
lean_ctor_set(x_700, 7, x_672);
lean_ctor_set(x_700, 8, x_673);
lean_ctor_set(x_700, 9, x_674);
lean_ctor_set(x_700, 10, x_675);
lean_ctor_set(x_700, 11, x_676);
x_701 = lean_st_ref_set(x_3, x_700, x_665);
x_702 = lean_ctor_get(x_701, 1);
lean_inc(x_702);
lean_dec(x_701);
x_619 = x_660;
x_620 = x_702;
goto block_637;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_703 = lean_box(0);
x_704 = lean_array_uset(x_679, x_683, x_703);
lean_inc(x_660);
x_705 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_616, x_660, x_684);
x_706 = lean_array_uset(x_704, x_683, x_705);
lean_ctor_set(x_664, 1, x_706);
x_707 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_707, 0, x_666);
lean_ctor_set(x_707, 1, x_664);
lean_ctor_set(x_707, 2, x_667);
lean_ctor_set(x_707, 3, x_668);
lean_ctor_set(x_707, 4, x_669);
lean_ctor_set(x_707, 5, x_670);
lean_ctor_set(x_707, 6, x_671);
lean_ctor_set(x_707, 7, x_672);
lean_ctor_set(x_707, 8, x_673);
lean_ctor_set(x_707, 9, x_674);
lean_ctor_set(x_707, 10, x_675);
lean_ctor_set(x_707, 11, x_676);
x_708 = lean_st_ref_set(x_3, x_707, x_665);
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
x_619 = x_660;
x_620 = x_709;
goto block_637;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; size_t x_713; size_t x_714; size_t x_715; lean_object* x_716; uint8_t x_717; 
x_710 = lean_ctor_get(x_664, 0);
x_711 = lean_ctor_get(x_664, 1);
lean_inc(x_711);
lean_inc(x_710);
lean_dec(x_664);
x_712 = lean_array_get_size(x_711);
x_713 = lean_usize_of_nat(x_712);
lean_dec(x_712);
x_714 = lean_usize_sub(x_713, x_654);
x_715 = lean_usize_land(x_652, x_714);
x_716 = lean_array_uget(x_711, x_715);
x_717 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_616, x_716);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
x_718 = lean_unsigned_to_nat(1u);
x_719 = lean_nat_add(x_710, x_718);
lean_dec(x_710);
lean_inc(x_660);
x_720 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_720, 0, x_616);
lean_ctor_set(x_720, 1, x_660);
lean_ctor_set(x_720, 2, x_716);
x_721 = lean_array_uset(x_711, x_715, x_720);
x_722 = lean_unsigned_to_nat(4u);
x_723 = lean_nat_mul(x_719, x_722);
x_724 = lean_unsigned_to_nat(3u);
x_725 = lean_nat_div(x_723, x_724);
lean_dec(x_723);
x_726 = lean_array_get_size(x_721);
x_727 = lean_nat_dec_le(x_725, x_726);
lean_dec(x_726);
lean_dec(x_725);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_721);
x_729 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_730, 0, x_666);
lean_ctor_set(x_730, 1, x_729);
lean_ctor_set(x_730, 2, x_667);
lean_ctor_set(x_730, 3, x_668);
lean_ctor_set(x_730, 4, x_669);
lean_ctor_set(x_730, 5, x_670);
lean_ctor_set(x_730, 6, x_671);
lean_ctor_set(x_730, 7, x_672);
lean_ctor_set(x_730, 8, x_673);
lean_ctor_set(x_730, 9, x_674);
lean_ctor_set(x_730, 10, x_675);
lean_ctor_set(x_730, 11, x_676);
x_731 = lean_st_ref_set(x_3, x_730, x_665);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec(x_731);
x_619 = x_660;
x_620 = x_732;
goto block_637;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_719);
lean_ctor_set(x_733, 1, x_721);
x_734 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_734, 0, x_666);
lean_ctor_set(x_734, 1, x_733);
lean_ctor_set(x_734, 2, x_667);
lean_ctor_set(x_734, 3, x_668);
lean_ctor_set(x_734, 4, x_669);
lean_ctor_set(x_734, 5, x_670);
lean_ctor_set(x_734, 6, x_671);
lean_ctor_set(x_734, 7, x_672);
lean_ctor_set(x_734, 8, x_673);
lean_ctor_set(x_734, 9, x_674);
lean_ctor_set(x_734, 10, x_675);
lean_ctor_set(x_734, 11, x_676);
x_735 = lean_st_ref_set(x_3, x_734, x_665);
x_736 = lean_ctor_get(x_735, 1);
lean_inc(x_736);
lean_dec(x_735);
x_619 = x_660;
x_620 = x_736;
goto block_637;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_737 = lean_box(0);
x_738 = lean_array_uset(x_711, x_715, x_737);
lean_inc(x_660);
x_739 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_616, x_660, x_716);
x_740 = lean_array_uset(x_738, x_715, x_739);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_710);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_742, 0, x_666);
lean_ctor_set(x_742, 1, x_741);
lean_ctor_set(x_742, 2, x_667);
lean_ctor_set(x_742, 3, x_668);
lean_ctor_set(x_742, 4, x_669);
lean_ctor_set(x_742, 5, x_670);
lean_ctor_set(x_742, 6, x_671);
lean_ctor_set(x_742, 7, x_672);
lean_ctor_set(x_742, 8, x_673);
lean_ctor_set(x_742, 9, x_674);
lean_ctor_set(x_742, 10, x_675);
lean_ctor_set(x_742, 11, x_676);
x_743 = lean_st_ref_set(x_3, x_742, x_665);
x_744 = lean_ctor_get(x_743, 1);
lean_inc(x_744);
lean_dec(x_743);
x_619 = x_660;
x_620 = x_744;
goto block_637;
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_659);
if (x_745 == 0)
{
return x_659;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_659, 0);
x_747 = lean_ctor_get(x_659, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_659);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
else
{
lean_object* x_749; 
lean_dec(x_616);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_749 = lean_ctor_get(x_658, 0);
lean_inc(x_749);
lean_dec(x_658);
x_619 = x_749;
x_620 = x_642;
goto block_637;
}
}
}
block_870:
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint64_t x_765; uint64_t x_766; uint64_t x_767; uint64_t x_768; uint64_t x_769; uint64_t x_770; uint64_t x_771; size_t x_772; size_t x_773; size_t x_774; size_t x_775; size_t x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_758);
x_759 = lean_st_ref_get(x_3, x_8);
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_760, 1);
lean_inc(x_761);
lean_dec(x_760);
x_762 = lean_ctor_get(x_759, 1);
lean_inc(x_762);
lean_dec(x_759);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = lean_array_get_size(x_763);
x_765 = l_Lean_Expr_hash(x_615);
x_766 = 32;
x_767 = lean_uint64_shift_right(x_765, x_766);
x_768 = lean_uint64_xor(x_765, x_767);
x_769 = 16;
x_770 = lean_uint64_shift_right(x_768, x_769);
x_771 = lean_uint64_xor(x_768, x_770);
x_772 = lean_uint64_to_usize(x_771);
x_773 = lean_usize_of_nat(x_764);
lean_dec(x_764);
x_774 = 1;
x_775 = lean_usize_sub(x_773, x_774);
x_776 = lean_usize_land(x_772, x_775);
x_777 = lean_array_uget(x_763, x_776);
lean_dec(x_763);
x_778 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_615, x_777);
lean_dec(x_777);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_615);
x_779 = l_Lean_Meta_Closure_collectExprAux(x_615, x_2, x_3, x_4, x_5, x_6, x_7, x_762);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; 
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
lean_dec(x_779);
x_782 = lean_st_ref_take(x_3, x_781);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_783, 1);
lean_inc(x_784);
x_785 = lean_ctor_get(x_782, 1);
lean_inc(x_785);
lean_dec(x_782);
x_786 = lean_ctor_get(x_783, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_783, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_783, 3);
lean_inc(x_788);
x_789 = lean_ctor_get(x_783, 4);
lean_inc(x_789);
x_790 = lean_ctor_get(x_783, 5);
lean_inc(x_790);
x_791 = lean_ctor_get(x_783, 6);
lean_inc(x_791);
x_792 = lean_ctor_get(x_783, 7);
lean_inc(x_792);
x_793 = lean_ctor_get(x_783, 8);
lean_inc(x_793);
x_794 = lean_ctor_get(x_783, 9);
lean_inc(x_794);
x_795 = lean_ctor_get(x_783, 10);
lean_inc(x_795);
x_796 = lean_ctor_get(x_783, 11);
lean_inc(x_796);
lean_dec(x_783);
x_797 = !lean_is_exclusive(x_784);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; size_t x_801; size_t x_802; size_t x_803; lean_object* x_804; uint8_t x_805; 
x_798 = lean_ctor_get(x_784, 0);
x_799 = lean_ctor_get(x_784, 1);
x_800 = lean_array_get_size(x_799);
x_801 = lean_usize_of_nat(x_800);
lean_dec(x_800);
x_802 = lean_usize_sub(x_801, x_774);
x_803 = lean_usize_land(x_772, x_802);
x_804 = lean_array_uget(x_799, x_803);
x_805 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_615, x_804);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_798, x_806);
lean_dec(x_798);
lean_inc(x_780);
x_808 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_808, 0, x_615);
lean_ctor_set(x_808, 1, x_780);
lean_ctor_set(x_808, 2, x_804);
x_809 = lean_array_uset(x_799, x_803, x_808);
x_810 = lean_unsigned_to_nat(4u);
x_811 = lean_nat_mul(x_807, x_810);
x_812 = lean_unsigned_to_nat(3u);
x_813 = lean_nat_div(x_811, x_812);
lean_dec(x_811);
x_814 = lean_array_get_size(x_809);
x_815 = lean_nat_dec_le(x_813, x_814);
lean_dec(x_814);
lean_dec(x_813);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_816 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_809);
lean_ctor_set(x_784, 1, x_816);
lean_ctor_set(x_784, 0, x_807);
x_817 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_817, 0, x_786);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_787);
lean_ctor_set(x_817, 3, x_788);
lean_ctor_set(x_817, 4, x_789);
lean_ctor_set(x_817, 5, x_790);
lean_ctor_set(x_817, 6, x_791);
lean_ctor_set(x_817, 7, x_792);
lean_ctor_set(x_817, 8, x_793);
lean_ctor_set(x_817, 9, x_794);
lean_ctor_set(x_817, 10, x_795);
lean_ctor_set(x_817, 11, x_796);
x_818 = lean_st_ref_set(x_3, x_817, x_785);
x_819 = lean_ctor_get(x_818, 1);
lean_inc(x_819);
lean_dec(x_818);
x_617 = x_780;
x_618 = x_819;
goto block_757;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
lean_ctor_set(x_784, 1, x_809);
lean_ctor_set(x_784, 0, x_807);
x_820 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_820, 0, x_786);
lean_ctor_set(x_820, 1, x_784);
lean_ctor_set(x_820, 2, x_787);
lean_ctor_set(x_820, 3, x_788);
lean_ctor_set(x_820, 4, x_789);
lean_ctor_set(x_820, 5, x_790);
lean_ctor_set(x_820, 6, x_791);
lean_ctor_set(x_820, 7, x_792);
lean_ctor_set(x_820, 8, x_793);
lean_ctor_set(x_820, 9, x_794);
lean_ctor_set(x_820, 10, x_795);
lean_ctor_set(x_820, 11, x_796);
x_821 = lean_st_ref_set(x_3, x_820, x_785);
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec(x_821);
x_617 = x_780;
x_618 = x_822;
goto block_757;
}
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_823 = lean_box(0);
x_824 = lean_array_uset(x_799, x_803, x_823);
lean_inc(x_780);
x_825 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_615, x_780, x_804);
x_826 = lean_array_uset(x_824, x_803, x_825);
lean_ctor_set(x_784, 1, x_826);
x_827 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_827, 0, x_786);
lean_ctor_set(x_827, 1, x_784);
lean_ctor_set(x_827, 2, x_787);
lean_ctor_set(x_827, 3, x_788);
lean_ctor_set(x_827, 4, x_789);
lean_ctor_set(x_827, 5, x_790);
lean_ctor_set(x_827, 6, x_791);
lean_ctor_set(x_827, 7, x_792);
lean_ctor_set(x_827, 8, x_793);
lean_ctor_set(x_827, 9, x_794);
lean_ctor_set(x_827, 10, x_795);
lean_ctor_set(x_827, 11, x_796);
x_828 = lean_st_ref_set(x_3, x_827, x_785);
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec(x_828);
x_617 = x_780;
x_618 = x_829;
goto block_757;
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; size_t x_833; size_t x_834; size_t x_835; lean_object* x_836; uint8_t x_837; 
x_830 = lean_ctor_get(x_784, 0);
x_831 = lean_ctor_get(x_784, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_784);
x_832 = lean_array_get_size(x_831);
x_833 = lean_usize_of_nat(x_832);
lean_dec(x_832);
x_834 = lean_usize_sub(x_833, x_774);
x_835 = lean_usize_land(x_772, x_834);
x_836 = lean_array_uget(x_831, x_835);
x_837 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_615, x_836);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; uint8_t x_847; 
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_830, x_838);
lean_dec(x_830);
lean_inc(x_780);
x_840 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_840, 0, x_615);
lean_ctor_set(x_840, 1, x_780);
lean_ctor_set(x_840, 2, x_836);
x_841 = lean_array_uset(x_831, x_835, x_840);
x_842 = lean_unsigned_to_nat(4u);
x_843 = lean_nat_mul(x_839, x_842);
x_844 = lean_unsigned_to_nat(3u);
x_845 = lean_nat_div(x_843, x_844);
lean_dec(x_843);
x_846 = lean_array_get_size(x_841);
x_847 = lean_nat_dec_le(x_845, x_846);
lean_dec(x_846);
lean_dec(x_845);
if (x_847 == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_848 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_841);
x_849 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_849, 0, x_839);
lean_ctor_set(x_849, 1, x_848);
x_850 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_850, 0, x_786);
lean_ctor_set(x_850, 1, x_849);
lean_ctor_set(x_850, 2, x_787);
lean_ctor_set(x_850, 3, x_788);
lean_ctor_set(x_850, 4, x_789);
lean_ctor_set(x_850, 5, x_790);
lean_ctor_set(x_850, 6, x_791);
lean_ctor_set(x_850, 7, x_792);
lean_ctor_set(x_850, 8, x_793);
lean_ctor_set(x_850, 9, x_794);
lean_ctor_set(x_850, 10, x_795);
lean_ctor_set(x_850, 11, x_796);
x_851 = lean_st_ref_set(x_3, x_850, x_785);
x_852 = lean_ctor_get(x_851, 1);
lean_inc(x_852);
lean_dec(x_851);
x_617 = x_780;
x_618 = x_852;
goto block_757;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_839);
lean_ctor_set(x_853, 1, x_841);
x_854 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_854, 0, x_786);
lean_ctor_set(x_854, 1, x_853);
lean_ctor_set(x_854, 2, x_787);
lean_ctor_set(x_854, 3, x_788);
lean_ctor_set(x_854, 4, x_789);
lean_ctor_set(x_854, 5, x_790);
lean_ctor_set(x_854, 6, x_791);
lean_ctor_set(x_854, 7, x_792);
lean_ctor_set(x_854, 8, x_793);
lean_ctor_set(x_854, 9, x_794);
lean_ctor_set(x_854, 10, x_795);
lean_ctor_set(x_854, 11, x_796);
x_855 = lean_st_ref_set(x_3, x_854, x_785);
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
lean_dec(x_855);
x_617 = x_780;
x_618 = x_856;
goto block_757;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_857 = lean_box(0);
x_858 = lean_array_uset(x_831, x_835, x_857);
lean_inc(x_780);
x_859 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_615, x_780, x_836);
x_860 = lean_array_uset(x_858, x_835, x_859);
x_861 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_861, 0, x_830);
lean_ctor_set(x_861, 1, x_860);
x_862 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_862, 0, x_786);
lean_ctor_set(x_862, 1, x_861);
lean_ctor_set(x_862, 2, x_787);
lean_ctor_set(x_862, 3, x_788);
lean_ctor_set(x_862, 4, x_789);
lean_ctor_set(x_862, 5, x_790);
lean_ctor_set(x_862, 6, x_791);
lean_ctor_set(x_862, 7, x_792);
lean_ctor_set(x_862, 8, x_793);
lean_ctor_set(x_862, 9, x_794);
lean_ctor_set(x_862, 10, x_795);
lean_ctor_set(x_862, 11, x_796);
x_863 = lean_st_ref_set(x_3, x_862, x_785);
x_864 = lean_ctor_get(x_863, 1);
lean_inc(x_864);
lean_dec(x_863);
x_617 = x_780;
x_618 = x_864;
goto block_757;
}
}
}
else
{
uint8_t x_865; 
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_865 = !lean_is_exclusive(x_779);
if (x_865 == 0)
{
return x_779;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_779, 0);
x_867 = lean_ctor_get(x_779, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_779);
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_866);
lean_ctor_set(x_868, 1, x_867);
return x_868;
}
}
}
else
{
lean_object* x_869; 
lean_dec(x_615);
x_869 = lean_ctor_get(x_778, 0);
lean_inc(x_869);
lean_dec(x_778);
x_617 = x_869;
x_618 = x_762;
goto block_757;
}
}
}
case 6:
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_1026; uint8_t x_1139; 
x_877 = lean_ctor_get(x_1, 1);
lean_inc(x_877);
x_878 = lean_ctor_get(x_1, 2);
lean_inc(x_878);
x_1139 = l_Lean_Expr_hasLevelParam(x_877);
if (x_1139 == 0)
{
uint8_t x_1140; 
x_1140 = l_Lean_Expr_hasFVar(x_877);
if (x_1140 == 0)
{
uint8_t x_1141; 
x_1141 = l_Lean_Expr_hasMVar(x_877);
if (x_1141 == 0)
{
x_879 = x_877;
x_880 = x_8;
goto block_1025;
}
else
{
lean_object* x_1142; 
x_1142 = lean_box(0);
x_1026 = x_1142;
goto block_1138;
}
}
else
{
lean_object* x_1143; 
x_1143 = lean_box(0);
x_1026 = x_1143;
goto block_1138;
}
}
else
{
lean_object* x_1144; 
x_1144 = lean_box(0);
x_1026 = x_1144;
goto block_1138;
}
block_1025:
{
lean_object* x_881; lean_object* x_882; lean_object* x_906; uint8_t x_1019; 
x_1019 = l_Lean_Expr_hasLevelParam(x_878);
if (x_1019 == 0)
{
uint8_t x_1020; 
x_1020 = l_Lean_Expr_hasFVar(x_878);
if (x_1020 == 0)
{
uint8_t x_1021; 
x_1021 = l_Lean_Expr_hasMVar(x_878);
if (x_1021 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_881 = x_878;
x_882 = x_880;
goto block_905;
}
else
{
lean_object* x_1022; 
x_1022 = lean_box(0);
x_906 = x_1022;
goto block_1018;
}
}
else
{
lean_object* x_1023; 
x_1023 = lean_box(0);
x_906 = x_1023;
goto block_1018;
}
}
else
{
lean_object* x_1024; 
x_1024 = lean_box(0);
x_906 = x_1024;
goto block_1018;
}
block_905:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; lean_object* x_887; size_t x_888; size_t x_889; uint8_t x_890; 
x_883 = lean_ctor_get(x_1, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_1, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_1, 2);
lean_inc(x_885);
x_886 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_885);
lean_inc(x_884);
lean_inc(x_883);
x_887 = l_Lean_Expr_lam___override(x_883, x_884, x_885, x_886);
x_888 = lean_ptr_addr(x_884);
lean_dec(x_884);
x_889 = lean_ptr_addr(x_879);
x_890 = lean_usize_dec_eq(x_888, x_889);
if (x_890 == 0)
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_887);
lean_dec(x_885);
x_891 = l_Lean_Expr_lam___override(x_883, x_879, x_881, x_886);
x_892 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_882);
return x_892;
}
else
{
size_t x_893; size_t x_894; uint8_t x_895; 
x_893 = lean_ptr_addr(x_885);
lean_dec(x_885);
x_894 = lean_ptr_addr(x_881);
x_895 = lean_usize_dec_eq(x_893, x_894);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; 
lean_dec(x_887);
x_896 = l_Lean_Expr_lam___override(x_883, x_879, x_881, x_886);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_896);
lean_ctor_set(x_897, 1, x_882);
return x_897;
}
else
{
uint8_t x_898; 
x_898 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_886, x_886);
if (x_898 == 0)
{
lean_object* x_899; lean_object* x_900; 
lean_dec(x_887);
x_899 = l_Lean_Expr_lam___override(x_883, x_879, x_881, x_886);
x_900 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_882);
return x_900;
}
else
{
lean_object* x_901; 
lean_dec(x_883);
lean_dec(x_881);
lean_dec(x_879);
x_901 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_901, 0, x_887);
lean_ctor_set(x_901, 1, x_882);
return x_901;
}
}
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_881);
lean_dec(x_879);
lean_dec(x_1);
x_902 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_903 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_902);
x_904 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_882);
return x_904;
}
}
block_1018:
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; uint64_t x_913; uint64_t x_914; uint64_t x_915; uint64_t x_916; uint64_t x_917; uint64_t x_918; uint64_t x_919; size_t x_920; size_t x_921; size_t x_922; size_t x_923; size_t x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_906);
x_907 = lean_st_ref_get(x_3, x_880);
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_908, 1);
lean_inc(x_909);
lean_dec(x_908);
x_910 = lean_ctor_get(x_907, 1);
lean_inc(x_910);
lean_dec(x_907);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
lean_dec(x_909);
x_912 = lean_array_get_size(x_911);
x_913 = l_Lean_Expr_hash(x_878);
x_914 = 32;
x_915 = lean_uint64_shift_right(x_913, x_914);
x_916 = lean_uint64_xor(x_913, x_915);
x_917 = 16;
x_918 = lean_uint64_shift_right(x_916, x_917);
x_919 = lean_uint64_xor(x_916, x_918);
x_920 = lean_uint64_to_usize(x_919);
x_921 = lean_usize_of_nat(x_912);
lean_dec(x_912);
x_922 = 1;
x_923 = lean_usize_sub(x_921, x_922);
x_924 = lean_usize_land(x_920, x_923);
x_925 = lean_array_uget(x_911, x_924);
lean_dec(x_911);
x_926 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_878, x_925);
lean_dec(x_925);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; 
lean_inc(x_878);
x_927 = l_Lean_Meta_Closure_collectExprAux(x_878, x_2, x_3, x_4, x_5, x_6, x_7, x_910);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; uint8_t x_945; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = lean_st_ref_take(x_3, x_929);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_931, 1);
lean_inc(x_932);
x_933 = lean_ctor_get(x_930, 1);
lean_inc(x_933);
lean_dec(x_930);
x_934 = lean_ctor_get(x_931, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_931, 2);
lean_inc(x_935);
x_936 = lean_ctor_get(x_931, 3);
lean_inc(x_936);
x_937 = lean_ctor_get(x_931, 4);
lean_inc(x_937);
x_938 = lean_ctor_get(x_931, 5);
lean_inc(x_938);
x_939 = lean_ctor_get(x_931, 6);
lean_inc(x_939);
x_940 = lean_ctor_get(x_931, 7);
lean_inc(x_940);
x_941 = lean_ctor_get(x_931, 8);
lean_inc(x_941);
x_942 = lean_ctor_get(x_931, 9);
lean_inc(x_942);
x_943 = lean_ctor_get(x_931, 10);
lean_inc(x_943);
x_944 = lean_ctor_get(x_931, 11);
lean_inc(x_944);
lean_dec(x_931);
x_945 = !lean_is_exclusive(x_932);
if (x_945 == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; size_t x_949; size_t x_950; size_t x_951; lean_object* x_952; uint8_t x_953; 
x_946 = lean_ctor_get(x_932, 0);
x_947 = lean_ctor_get(x_932, 1);
x_948 = lean_array_get_size(x_947);
x_949 = lean_usize_of_nat(x_948);
lean_dec(x_948);
x_950 = lean_usize_sub(x_949, x_922);
x_951 = lean_usize_land(x_920, x_950);
x_952 = lean_array_uget(x_947, x_951);
x_953 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_878, x_952);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; 
x_954 = lean_unsigned_to_nat(1u);
x_955 = lean_nat_add(x_946, x_954);
lean_dec(x_946);
lean_inc(x_928);
x_956 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_956, 0, x_878);
lean_ctor_set(x_956, 1, x_928);
lean_ctor_set(x_956, 2, x_952);
x_957 = lean_array_uset(x_947, x_951, x_956);
x_958 = lean_unsigned_to_nat(4u);
x_959 = lean_nat_mul(x_955, x_958);
x_960 = lean_unsigned_to_nat(3u);
x_961 = lean_nat_div(x_959, x_960);
lean_dec(x_959);
x_962 = lean_array_get_size(x_957);
x_963 = lean_nat_dec_le(x_961, x_962);
lean_dec(x_962);
lean_dec(x_961);
if (x_963 == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_964 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_957);
lean_ctor_set(x_932, 1, x_964);
lean_ctor_set(x_932, 0, x_955);
x_965 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_965, 0, x_934);
lean_ctor_set(x_965, 1, x_932);
lean_ctor_set(x_965, 2, x_935);
lean_ctor_set(x_965, 3, x_936);
lean_ctor_set(x_965, 4, x_937);
lean_ctor_set(x_965, 5, x_938);
lean_ctor_set(x_965, 6, x_939);
lean_ctor_set(x_965, 7, x_940);
lean_ctor_set(x_965, 8, x_941);
lean_ctor_set(x_965, 9, x_942);
lean_ctor_set(x_965, 10, x_943);
lean_ctor_set(x_965, 11, x_944);
x_966 = lean_st_ref_set(x_3, x_965, x_933);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
lean_dec(x_966);
x_881 = x_928;
x_882 = x_967;
goto block_905;
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_ctor_set(x_932, 1, x_957);
lean_ctor_set(x_932, 0, x_955);
x_968 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_968, 0, x_934);
lean_ctor_set(x_968, 1, x_932);
lean_ctor_set(x_968, 2, x_935);
lean_ctor_set(x_968, 3, x_936);
lean_ctor_set(x_968, 4, x_937);
lean_ctor_set(x_968, 5, x_938);
lean_ctor_set(x_968, 6, x_939);
lean_ctor_set(x_968, 7, x_940);
lean_ctor_set(x_968, 8, x_941);
lean_ctor_set(x_968, 9, x_942);
lean_ctor_set(x_968, 10, x_943);
lean_ctor_set(x_968, 11, x_944);
x_969 = lean_st_ref_set(x_3, x_968, x_933);
x_970 = lean_ctor_get(x_969, 1);
lean_inc(x_970);
lean_dec(x_969);
x_881 = x_928;
x_882 = x_970;
goto block_905;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_971 = lean_box(0);
x_972 = lean_array_uset(x_947, x_951, x_971);
lean_inc(x_928);
x_973 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_878, x_928, x_952);
x_974 = lean_array_uset(x_972, x_951, x_973);
lean_ctor_set(x_932, 1, x_974);
x_975 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_975, 0, x_934);
lean_ctor_set(x_975, 1, x_932);
lean_ctor_set(x_975, 2, x_935);
lean_ctor_set(x_975, 3, x_936);
lean_ctor_set(x_975, 4, x_937);
lean_ctor_set(x_975, 5, x_938);
lean_ctor_set(x_975, 6, x_939);
lean_ctor_set(x_975, 7, x_940);
lean_ctor_set(x_975, 8, x_941);
lean_ctor_set(x_975, 9, x_942);
lean_ctor_set(x_975, 10, x_943);
lean_ctor_set(x_975, 11, x_944);
x_976 = lean_st_ref_set(x_3, x_975, x_933);
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_881 = x_928;
x_882 = x_977;
goto block_905;
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; size_t x_981; size_t x_982; size_t x_983; lean_object* x_984; uint8_t x_985; 
x_978 = lean_ctor_get(x_932, 0);
x_979 = lean_ctor_get(x_932, 1);
lean_inc(x_979);
lean_inc(x_978);
lean_dec(x_932);
x_980 = lean_array_get_size(x_979);
x_981 = lean_usize_of_nat(x_980);
lean_dec(x_980);
x_982 = lean_usize_sub(x_981, x_922);
x_983 = lean_usize_land(x_920, x_982);
x_984 = lean_array_uget(x_979, x_983);
x_985 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_878, x_984);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; uint8_t x_995; 
x_986 = lean_unsigned_to_nat(1u);
x_987 = lean_nat_add(x_978, x_986);
lean_dec(x_978);
lean_inc(x_928);
x_988 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_988, 0, x_878);
lean_ctor_set(x_988, 1, x_928);
lean_ctor_set(x_988, 2, x_984);
x_989 = lean_array_uset(x_979, x_983, x_988);
x_990 = lean_unsigned_to_nat(4u);
x_991 = lean_nat_mul(x_987, x_990);
x_992 = lean_unsigned_to_nat(3u);
x_993 = lean_nat_div(x_991, x_992);
lean_dec(x_991);
x_994 = lean_array_get_size(x_989);
x_995 = lean_nat_dec_le(x_993, x_994);
lean_dec(x_994);
lean_dec(x_993);
if (x_995 == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_996 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_989);
x_997 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_997, 0, x_987);
lean_ctor_set(x_997, 1, x_996);
x_998 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_998, 0, x_934);
lean_ctor_set(x_998, 1, x_997);
lean_ctor_set(x_998, 2, x_935);
lean_ctor_set(x_998, 3, x_936);
lean_ctor_set(x_998, 4, x_937);
lean_ctor_set(x_998, 5, x_938);
lean_ctor_set(x_998, 6, x_939);
lean_ctor_set(x_998, 7, x_940);
lean_ctor_set(x_998, 8, x_941);
lean_ctor_set(x_998, 9, x_942);
lean_ctor_set(x_998, 10, x_943);
lean_ctor_set(x_998, 11, x_944);
x_999 = lean_st_ref_set(x_3, x_998, x_933);
x_1000 = lean_ctor_get(x_999, 1);
lean_inc(x_1000);
lean_dec(x_999);
x_881 = x_928;
x_882 = x_1000;
goto block_905;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_987);
lean_ctor_set(x_1001, 1, x_989);
x_1002 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1002, 0, x_934);
lean_ctor_set(x_1002, 1, x_1001);
lean_ctor_set(x_1002, 2, x_935);
lean_ctor_set(x_1002, 3, x_936);
lean_ctor_set(x_1002, 4, x_937);
lean_ctor_set(x_1002, 5, x_938);
lean_ctor_set(x_1002, 6, x_939);
lean_ctor_set(x_1002, 7, x_940);
lean_ctor_set(x_1002, 8, x_941);
lean_ctor_set(x_1002, 9, x_942);
lean_ctor_set(x_1002, 10, x_943);
lean_ctor_set(x_1002, 11, x_944);
x_1003 = lean_st_ref_set(x_3, x_1002, x_933);
x_1004 = lean_ctor_get(x_1003, 1);
lean_inc(x_1004);
lean_dec(x_1003);
x_881 = x_928;
x_882 = x_1004;
goto block_905;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1005 = lean_box(0);
x_1006 = lean_array_uset(x_979, x_983, x_1005);
lean_inc(x_928);
x_1007 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_878, x_928, x_984);
x_1008 = lean_array_uset(x_1006, x_983, x_1007);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_978);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1010, 0, x_934);
lean_ctor_set(x_1010, 1, x_1009);
lean_ctor_set(x_1010, 2, x_935);
lean_ctor_set(x_1010, 3, x_936);
lean_ctor_set(x_1010, 4, x_937);
lean_ctor_set(x_1010, 5, x_938);
lean_ctor_set(x_1010, 6, x_939);
lean_ctor_set(x_1010, 7, x_940);
lean_ctor_set(x_1010, 8, x_941);
lean_ctor_set(x_1010, 9, x_942);
lean_ctor_set(x_1010, 10, x_943);
lean_ctor_set(x_1010, 11, x_944);
x_1011 = lean_st_ref_set(x_3, x_1010, x_933);
x_1012 = lean_ctor_get(x_1011, 1);
lean_inc(x_1012);
lean_dec(x_1011);
x_881 = x_928;
x_882 = x_1012;
goto block_905;
}
}
}
else
{
uint8_t x_1013; 
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_1);
x_1013 = !lean_is_exclusive(x_927);
if (x_1013 == 0)
{
return x_927;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_927, 0);
x_1015 = lean_ctor_get(x_927, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_927);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
else
{
lean_object* x_1017; 
lean_dec(x_878);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1017 = lean_ctor_get(x_926, 0);
lean_inc(x_1017);
lean_dec(x_926);
x_881 = x_1017;
x_882 = x_910;
goto block_905;
}
}
}
block_1138:
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; uint64_t x_1033; uint64_t x_1034; uint64_t x_1035; uint64_t x_1036; uint64_t x_1037; uint64_t x_1038; uint64_t x_1039; size_t x_1040; size_t x_1041; size_t x_1042; size_t x_1043; size_t x_1044; lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_1026);
x_1027 = lean_st_ref_get(x_3, x_8);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1028, 1);
lean_inc(x_1029);
lean_dec(x_1028);
x_1030 = lean_ctor_get(x_1027, 1);
lean_inc(x_1030);
lean_dec(x_1027);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = lean_array_get_size(x_1031);
x_1033 = l_Lean_Expr_hash(x_877);
x_1034 = 32;
x_1035 = lean_uint64_shift_right(x_1033, x_1034);
x_1036 = lean_uint64_xor(x_1033, x_1035);
x_1037 = 16;
x_1038 = lean_uint64_shift_right(x_1036, x_1037);
x_1039 = lean_uint64_xor(x_1036, x_1038);
x_1040 = lean_uint64_to_usize(x_1039);
x_1041 = lean_usize_of_nat(x_1032);
lean_dec(x_1032);
x_1042 = 1;
x_1043 = lean_usize_sub(x_1041, x_1042);
x_1044 = lean_usize_land(x_1040, x_1043);
x_1045 = lean_array_uget(x_1031, x_1044);
lean_dec(x_1031);
x_1046 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_877, x_1045);
lean_dec(x_1045);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_877);
x_1047 = l_Lean_Meta_Closure_collectExprAux(x_877, x_2, x_3, x_4, x_5, x_6, x_7, x_1030);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; uint8_t x_1065; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec(x_1047);
x_1050 = lean_st_ref_take(x_3, x_1049);
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1051, 1);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1050, 1);
lean_inc(x_1053);
lean_dec(x_1050);
x_1054 = lean_ctor_get(x_1051, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1051, 2);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1051, 3);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1051, 4);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1051, 5);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1051, 6);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1051, 7);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1051, 8);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1051, 9);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1051, 10);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1051, 11);
lean_inc(x_1064);
lean_dec(x_1051);
x_1065 = !lean_is_exclusive(x_1052);
if (x_1065 == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; size_t x_1069; size_t x_1070; size_t x_1071; lean_object* x_1072; uint8_t x_1073; 
x_1066 = lean_ctor_get(x_1052, 0);
x_1067 = lean_ctor_get(x_1052, 1);
x_1068 = lean_array_get_size(x_1067);
x_1069 = lean_usize_of_nat(x_1068);
lean_dec(x_1068);
x_1070 = lean_usize_sub(x_1069, x_1042);
x_1071 = lean_usize_land(x_1040, x_1070);
x_1072 = lean_array_uget(x_1067, x_1071);
x_1073 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_877, x_1072);
if (x_1073 == 0)
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; uint8_t x_1083; 
x_1074 = lean_unsigned_to_nat(1u);
x_1075 = lean_nat_add(x_1066, x_1074);
lean_dec(x_1066);
lean_inc(x_1048);
x_1076 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1076, 0, x_877);
lean_ctor_set(x_1076, 1, x_1048);
lean_ctor_set(x_1076, 2, x_1072);
x_1077 = lean_array_uset(x_1067, x_1071, x_1076);
x_1078 = lean_unsigned_to_nat(4u);
x_1079 = lean_nat_mul(x_1075, x_1078);
x_1080 = lean_unsigned_to_nat(3u);
x_1081 = lean_nat_div(x_1079, x_1080);
lean_dec(x_1079);
x_1082 = lean_array_get_size(x_1077);
x_1083 = lean_nat_dec_le(x_1081, x_1082);
lean_dec(x_1082);
lean_dec(x_1081);
if (x_1083 == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1084 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1077);
lean_ctor_set(x_1052, 1, x_1084);
lean_ctor_set(x_1052, 0, x_1075);
x_1085 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1085, 0, x_1054);
lean_ctor_set(x_1085, 1, x_1052);
lean_ctor_set(x_1085, 2, x_1055);
lean_ctor_set(x_1085, 3, x_1056);
lean_ctor_set(x_1085, 4, x_1057);
lean_ctor_set(x_1085, 5, x_1058);
lean_ctor_set(x_1085, 6, x_1059);
lean_ctor_set(x_1085, 7, x_1060);
lean_ctor_set(x_1085, 8, x_1061);
lean_ctor_set(x_1085, 9, x_1062);
lean_ctor_set(x_1085, 10, x_1063);
lean_ctor_set(x_1085, 11, x_1064);
x_1086 = lean_st_ref_set(x_3, x_1085, x_1053);
x_1087 = lean_ctor_get(x_1086, 1);
lean_inc(x_1087);
lean_dec(x_1086);
x_879 = x_1048;
x_880 = x_1087;
goto block_1025;
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
lean_ctor_set(x_1052, 1, x_1077);
lean_ctor_set(x_1052, 0, x_1075);
x_1088 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1088, 0, x_1054);
lean_ctor_set(x_1088, 1, x_1052);
lean_ctor_set(x_1088, 2, x_1055);
lean_ctor_set(x_1088, 3, x_1056);
lean_ctor_set(x_1088, 4, x_1057);
lean_ctor_set(x_1088, 5, x_1058);
lean_ctor_set(x_1088, 6, x_1059);
lean_ctor_set(x_1088, 7, x_1060);
lean_ctor_set(x_1088, 8, x_1061);
lean_ctor_set(x_1088, 9, x_1062);
lean_ctor_set(x_1088, 10, x_1063);
lean_ctor_set(x_1088, 11, x_1064);
x_1089 = lean_st_ref_set(x_3, x_1088, x_1053);
x_1090 = lean_ctor_get(x_1089, 1);
lean_inc(x_1090);
lean_dec(x_1089);
x_879 = x_1048;
x_880 = x_1090;
goto block_1025;
}
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1091 = lean_box(0);
x_1092 = lean_array_uset(x_1067, x_1071, x_1091);
lean_inc(x_1048);
x_1093 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_877, x_1048, x_1072);
x_1094 = lean_array_uset(x_1092, x_1071, x_1093);
lean_ctor_set(x_1052, 1, x_1094);
x_1095 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1095, 0, x_1054);
lean_ctor_set(x_1095, 1, x_1052);
lean_ctor_set(x_1095, 2, x_1055);
lean_ctor_set(x_1095, 3, x_1056);
lean_ctor_set(x_1095, 4, x_1057);
lean_ctor_set(x_1095, 5, x_1058);
lean_ctor_set(x_1095, 6, x_1059);
lean_ctor_set(x_1095, 7, x_1060);
lean_ctor_set(x_1095, 8, x_1061);
lean_ctor_set(x_1095, 9, x_1062);
lean_ctor_set(x_1095, 10, x_1063);
lean_ctor_set(x_1095, 11, x_1064);
x_1096 = lean_st_ref_set(x_3, x_1095, x_1053);
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
lean_dec(x_1096);
x_879 = x_1048;
x_880 = x_1097;
goto block_1025;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; size_t x_1101; size_t x_1102; size_t x_1103; lean_object* x_1104; uint8_t x_1105; 
x_1098 = lean_ctor_get(x_1052, 0);
x_1099 = lean_ctor_get(x_1052, 1);
lean_inc(x_1099);
lean_inc(x_1098);
lean_dec(x_1052);
x_1100 = lean_array_get_size(x_1099);
x_1101 = lean_usize_of_nat(x_1100);
lean_dec(x_1100);
x_1102 = lean_usize_sub(x_1101, x_1042);
x_1103 = lean_usize_land(x_1040, x_1102);
x_1104 = lean_array_uget(x_1099, x_1103);
x_1105 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_877, x_1104);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; uint8_t x_1115; 
x_1106 = lean_unsigned_to_nat(1u);
x_1107 = lean_nat_add(x_1098, x_1106);
lean_dec(x_1098);
lean_inc(x_1048);
x_1108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1108, 0, x_877);
lean_ctor_set(x_1108, 1, x_1048);
lean_ctor_set(x_1108, 2, x_1104);
x_1109 = lean_array_uset(x_1099, x_1103, x_1108);
x_1110 = lean_unsigned_to_nat(4u);
x_1111 = lean_nat_mul(x_1107, x_1110);
x_1112 = lean_unsigned_to_nat(3u);
x_1113 = lean_nat_div(x_1111, x_1112);
lean_dec(x_1111);
x_1114 = lean_array_get_size(x_1109);
x_1115 = lean_nat_dec_le(x_1113, x_1114);
lean_dec(x_1114);
lean_dec(x_1113);
if (x_1115 == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1116 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1109);
x_1117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1117, 0, x_1107);
lean_ctor_set(x_1117, 1, x_1116);
x_1118 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1118, 0, x_1054);
lean_ctor_set(x_1118, 1, x_1117);
lean_ctor_set(x_1118, 2, x_1055);
lean_ctor_set(x_1118, 3, x_1056);
lean_ctor_set(x_1118, 4, x_1057);
lean_ctor_set(x_1118, 5, x_1058);
lean_ctor_set(x_1118, 6, x_1059);
lean_ctor_set(x_1118, 7, x_1060);
lean_ctor_set(x_1118, 8, x_1061);
lean_ctor_set(x_1118, 9, x_1062);
lean_ctor_set(x_1118, 10, x_1063);
lean_ctor_set(x_1118, 11, x_1064);
x_1119 = lean_st_ref_set(x_3, x_1118, x_1053);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
lean_dec(x_1119);
x_879 = x_1048;
x_880 = x_1120;
goto block_1025;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1121, 0, x_1107);
lean_ctor_set(x_1121, 1, x_1109);
x_1122 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1122, 0, x_1054);
lean_ctor_set(x_1122, 1, x_1121);
lean_ctor_set(x_1122, 2, x_1055);
lean_ctor_set(x_1122, 3, x_1056);
lean_ctor_set(x_1122, 4, x_1057);
lean_ctor_set(x_1122, 5, x_1058);
lean_ctor_set(x_1122, 6, x_1059);
lean_ctor_set(x_1122, 7, x_1060);
lean_ctor_set(x_1122, 8, x_1061);
lean_ctor_set(x_1122, 9, x_1062);
lean_ctor_set(x_1122, 10, x_1063);
lean_ctor_set(x_1122, 11, x_1064);
x_1123 = lean_st_ref_set(x_3, x_1122, x_1053);
x_1124 = lean_ctor_get(x_1123, 1);
lean_inc(x_1124);
lean_dec(x_1123);
x_879 = x_1048;
x_880 = x_1124;
goto block_1025;
}
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1125 = lean_box(0);
x_1126 = lean_array_uset(x_1099, x_1103, x_1125);
lean_inc(x_1048);
x_1127 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_877, x_1048, x_1104);
x_1128 = lean_array_uset(x_1126, x_1103, x_1127);
x_1129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1129, 0, x_1098);
lean_ctor_set(x_1129, 1, x_1128);
x_1130 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1130, 0, x_1054);
lean_ctor_set(x_1130, 1, x_1129);
lean_ctor_set(x_1130, 2, x_1055);
lean_ctor_set(x_1130, 3, x_1056);
lean_ctor_set(x_1130, 4, x_1057);
lean_ctor_set(x_1130, 5, x_1058);
lean_ctor_set(x_1130, 6, x_1059);
lean_ctor_set(x_1130, 7, x_1060);
lean_ctor_set(x_1130, 8, x_1061);
lean_ctor_set(x_1130, 9, x_1062);
lean_ctor_set(x_1130, 10, x_1063);
lean_ctor_set(x_1130, 11, x_1064);
x_1131 = lean_st_ref_set(x_3, x_1130, x_1053);
x_1132 = lean_ctor_get(x_1131, 1);
lean_inc(x_1132);
lean_dec(x_1131);
x_879 = x_1048;
x_880 = x_1132;
goto block_1025;
}
}
}
else
{
uint8_t x_1133; 
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1133 = !lean_is_exclusive(x_1047);
if (x_1133 == 0)
{
return x_1047;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1047, 0);
x_1135 = lean_ctor_get(x_1047, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1047);
x_1136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
return x_1136;
}
}
}
else
{
lean_object* x_1137; 
lean_dec(x_877);
x_1137 = lean_ctor_get(x_1046, 0);
lean_inc(x_1137);
lean_dec(x_1046);
x_879 = x_1137;
x_880 = x_1030;
goto block_1025;
}
}
}
case 7:
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1294; uint8_t x_1407; 
x_1145 = lean_ctor_get(x_1, 1);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1, 2);
lean_inc(x_1146);
x_1407 = l_Lean_Expr_hasLevelParam(x_1145);
if (x_1407 == 0)
{
uint8_t x_1408; 
x_1408 = l_Lean_Expr_hasFVar(x_1145);
if (x_1408 == 0)
{
uint8_t x_1409; 
x_1409 = l_Lean_Expr_hasMVar(x_1145);
if (x_1409 == 0)
{
x_1147 = x_1145;
x_1148 = x_8;
goto block_1293;
}
else
{
lean_object* x_1410; 
x_1410 = lean_box(0);
x_1294 = x_1410;
goto block_1406;
}
}
else
{
lean_object* x_1411; 
x_1411 = lean_box(0);
x_1294 = x_1411;
goto block_1406;
}
}
else
{
lean_object* x_1412; 
x_1412 = lean_box(0);
x_1294 = x_1412;
goto block_1406;
}
block_1293:
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1174; uint8_t x_1287; 
x_1287 = l_Lean_Expr_hasLevelParam(x_1146);
if (x_1287 == 0)
{
uint8_t x_1288; 
x_1288 = l_Lean_Expr_hasFVar(x_1146);
if (x_1288 == 0)
{
uint8_t x_1289; 
x_1289 = l_Lean_Expr_hasMVar(x_1146);
if (x_1289 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1149 = x_1146;
x_1150 = x_1148;
goto block_1173;
}
else
{
lean_object* x_1290; 
x_1290 = lean_box(0);
x_1174 = x_1290;
goto block_1286;
}
}
else
{
lean_object* x_1291; 
x_1291 = lean_box(0);
x_1174 = x_1291;
goto block_1286;
}
}
else
{
lean_object* x_1292; 
x_1292 = lean_box(0);
x_1174 = x_1292;
goto block_1286;
}
block_1173:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; uint8_t x_1154; lean_object* x_1155; size_t x_1156; size_t x_1157; uint8_t x_1158; 
x_1151 = lean_ctor_get(x_1, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1, 1);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1, 2);
lean_inc(x_1153);
x_1154 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_inc(x_1151);
x_1155 = l_Lean_Expr_forallE___override(x_1151, x_1152, x_1153, x_1154);
x_1156 = lean_ptr_addr(x_1152);
lean_dec(x_1152);
x_1157 = lean_ptr_addr(x_1147);
x_1158 = lean_usize_dec_eq(x_1156, x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_1155);
lean_dec(x_1153);
x_1159 = l_Lean_Expr_forallE___override(x_1151, x_1147, x_1149, x_1154);
x_1160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1160, 0, x_1159);
lean_ctor_set(x_1160, 1, x_1150);
return x_1160;
}
else
{
size_t x_1161; size_t x_1162; uint8_t x_1163; 
x_1161 = lean_ptr_addr(x_1153);
lean_dec(x_1153);
x_1162 = lean_ptr_addr(x_1149);
x_1163 = lean_usize_dec_eq(x_1161, x_1162);
if (x_1163 == 0)
{
lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1155);
x_1164 = l_Lean_Expr_forallE___override(x_1151, x_1147, x_1149, x_1154);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_1164);
lean_ctor_set(x_1165, 1, x_1150);
return x_1165;
}
else
{
uint8_t x_1166; 
x_1166 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_1154, x_1154);
if (x_1166 == 0)
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1155);
x_1167 = l_Lean_Expr_forallE___override(x_1151, x_1147, x_1149, x_1154);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_1167);
lean_ctor_set(x_1168, 1, x_1150);
return x_1168;
}
else
{
lean_object* x_1169; 
lean_dec(x_1151);
lean_dec(x_1149);
lean_dec(x_1147);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_1155);
lean_ctor_set(x_1169, 1, x_1150);
return x_1169;
}
}
}
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1149);
lean_dec(x_1147);
lean_dec(x_1);
x_1170 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_1171 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_1170);
x_1172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1150);
return x_1172;
}
}
block_1286:
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; uint64_t x_1181; uint64_t x_1182; uint64_t x_1183; uint64_t x_1184; uint64_t x_1185; uint64_t x_1186; uint64_t x_1187; size_t x_1188; size_t x_1189; size_t x_1190; size_t x_1191; size_t x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_1174);
x_1175 = lean_st_ref_get(x_3, x_1148);
x_1176 = lean_ctor_get(x_1175, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1176, 1);
lean_inc(x_1177);
lean_dec(x_1176);
x_1178 = lean_ctor_get(x_1175, 1);
lean_inc(x_1178);
lean_dec(x_1175);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1180 = lean_array_get_size(x_1179);
x_1181 = l_Lean_Expr_hash(x_1146);
x_1182 = 32;
x_1183 = lean_uint64_shift_right(x_1181, x_1182);
x_1184 = lean_uint64_xor(x_1181, x_1183);
x_1185 = 16;
x_1186 = lean_uint64_shift_right(x_1184, x_1185);
x_1187 = lean_uint64_xor(x_1184, x_1186);
x_1188 = lean_uint64_to_usize(x_1187);
x_1189 = lean_usize_of_nat(x_1180);
lean_dec(x_1180);
x_1190 = 1;
x_1191 = lean_usize_sub(x_1189, x_1190);
x_1192 = lean_usize_land(x_1188, x_1191);
x_1193 = lean_array_uget(x_1179, x_1192);
lean_dec(x_1179);
x_1194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1146, x_1193);
lean_dec(x_1193);
if (lean_obj_tag(x_1194) == 0)
{
lean_object* x_1195; 
lean_inc(x_1146);
x_1195 = l_Lean_Meta_Closure_collectExprAux(x_1146, x_2, x_3, x_4, x_5, x_6, x_7, x_1178);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
lean_dec(x_1195);
x_1198 = lean_st_ref_take(x_3, x_1197);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1199, 1);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1198, 1);
lean_inc(x_1201);
lean_dec(x_1198);
x_1202 = lean_ctor_get(x_1199, 0);
lean_inc(x_1202);
x_1203 = lean_ctor_get(x_1199, 2);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1199, 3);
lean_inc(x_1204);
x_1205 = lean_ctor_get(x_1199, 4);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_1199, 5);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1199, 6);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1199, 7);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1199, 8);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1199, 9);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1199, 10);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1199, 11);
lean_inc(x_1212);
lean_dec(x_1199);
x_1213 = !lean_is_exclusive(x_1200);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; size_t x_1217; size_t x_1218; size_t x_1219; lean_object* x_1220; uint8_t x_1221; 
x_1214 = lean_ctor_get(x_1200, 0);
x_1215 = lean_ctor_get(x_1200, 1);
x_1216 = lean_array_get_size(x_1215);
x_1217 = lean_usize_of_nat(x_1216);
lean_dec(x_1216);
x_1218 = lean_usize_sub(x_1217, x_1190);
x_1219 = lean_usize_land(x_1188, x_1218);
x_1220 = lean_array_uget(x_1215, x_1219);
x_1221 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1146, x_1220);
if (x_1221 == 0)
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; 
x_1222 = lean_unsigned_to_nat(1u);
x_1223 = lean_nat_add(x_1214, x_1222);
lean_dec(x_1214);
lean_inc(x_1196);
x_1224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1224, 0, x_1146);
lean_ctor_set(x_1224, 1, x_1196);
lean_ctor_set(x_1224, 2, x_1220);
x_1225 = lean_array_uset(x_1215, x_1219, x_1224);
x_1226 = lean_unsigned_to_nat(4u);
x_1227 = lean_nat_mul(x_1223, x_1226);
x_1228 = lean_unsigned_to_nat(3u);
x_1229 = lean_nat_div(x_1227, x_1228);
lean_dec(x_1227);
x_1230 = lean_array_get_size(x_1225);
x_1231 = lean_nat_dec_le(x_1229, x_1230);
lean_dec(x_1230);
lean_dec(x_1229);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1232 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1225);
lean_ctor_set(x_1200, 1, x_1232);
lean_ctor_set(x_1200, 0, x_1223);
x_1233 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1233, 0, x_1202);
lean_ctor_set(x_1233, 1, x_1200);
lean_ctor_set(x_1233, 2, x_1203);
lean_ctor_set(x_1233, 3, x_1204);
lean_ctor_set(x_1233, 4, x_1205);
lean_ctor_set(x_1233, 5, x_1206);
lean_ctor_set(x_1233, 6, x_1207);
lean_ctor_set(x_1233, 7, x_1208);
lean_ctor_set(x_1233, 8, x_1209);
lean_ctor_set(x_1233, 9, x_1210);
lean_ctor_set(x_1233, 10, x_1211);
lean_ctor_set(x_1233, 11, x_1212);
x_1234 = lean_st_ref_set(x_3, x_1233, x_1201);
x_1235 = lean_ctor_get(x_1234, 1);
lean_inc(x_1235);
lean_dec(x_1234);
x_1149 = x_1196;
x_1150 = x_1235;
goto block_1173;
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_ctor_set(x_1200, 1, x_1225);
lean_ctor_set(x_1200, 0, x_1223);
x_1236 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1236, 0, x_1202);
lean_ctor_set(x_1236, 1, x_1200);
lean_ctor_set(x_1236, 2, x_1203);
lean_ctor_set(x_1236, 3, x_1204);
lean_ctor_set(x_1236, 4, x_1205);
lean_ctor_set(x_1236, 5, x_1206);
lean_ctor_set(x_1236, 6, x_1207);
lean_ctor_set(x_1236, 7, x_1208);
lean_ctor_set(x_1236, 8, x_1209);
lean_ctor_set(x_1236, 9, x_1210);
lean_ctor_set(x_1236, 10, x_1211);
lean_ctor_set(x_1236, 11, x_1212);
x_1237 = lean_st_ref_set(x_3, x_1236, x_1201);
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
lean_dec(x_1237);
x_1149 = x_1196;
x_1150 = x_1238;
goto block_1173;
}
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1239 = lean_box(0);
x_1240 = lean_array_uset(x_1215, x_1219, x_1239);
lean_inc(x_1196);
x_1241 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1146, x_1196, x_1220);
x_1242 = lean_array_uset(x_1240, x_1219, x_1241);
lean_ctor_set(x_1200, 1, x_1242);
x_1243 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1243, 0, x_1202);
lean_ctor_set(x_1243, 1, x_1200);
lean_ctor_set(x_1243, 2, x_1203);
lean_ctor_set(x_1243, 3, x_1204);
lean_ctor_set(x_1243, 4, x_1205);
lean_ctor_set(x_1243, 5, x_1206);
lean_ctor_set(x_1243, 6, x_1207);
lean_ctor_set(x_1243, 7, x_1208);
lean_ctor_set(x_1243, 8, x_1209);
lean_ctor_set(x_1243, 9, x_1210);
lean_ctor_set(x_1243, 10, x_1211);
lean_ctor_set(x_1243, 11, x_1212);
x_1244 = lean_st_ref_set(x_3, x_1243, x_1201);
x_1245 = lean_ctor_get(x_1244, 1);
lean_inc(x_1245);
lean_dec(x_1244);
x_1149 = x_1196;
x_1150 = x_1245;
goto block_1173;
}
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; size_t x_1249; size_t x_1250; size_t x_1251; lean_object* x_1252; uint8_t x_1253; 
x_1246 = lean_ctor_get(x_1200, 0);
x_1247 = lean_ctor_get(x_1200, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1200);
x_1248 = lean_array_get_size(x_1247);
x_1249 = lean_usize_of_nat(x_1248);
lean_dec(x_1248);
x_1250 = lean_usize_sub(x_1249, x_1190);
x_1251 = lean_usize_land(x_1188, x_1250);
x_1252 = lean_array_uget(x_1247, x_1251);
x_1253 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1146, x_1252);
if (x_1253 == 0)
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; 
x_1254 = lean_unsigned_to_nat(1u);
x_1255 = lean_nat_add(x_1246, x_1254);
lean_dec(x_1246);
lean_inc(x_1196);
x_1256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1256, 0, x_1146);
lean_ctor_set(x_1256, 1, x_1196);
lean_ctor_set(x_1256, 2, x_1252);
x_1257 = lean_array_uset(x_1247, x_1251, x_1256);
x_1258 = lean_unsigned_to_nat(4u);
x_1259 = lean_nat_mul(x_1255, x_1258);
x_1260 = lean_unsigned_to_nat(3u);
x_1261 = lean_nat_div(x_1259, x_1260);
lean_dec(x_1259);
x_1262 = lean_array_get_size(x_1257);
x_1263 = lean_nat_dec_le(x_1261, x_1262);
lean_dec(x_1262);
lean_dec(x_1261);
if (x_1263 == 0)
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1264 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1257);
x_1265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1265, 0, x_1255);
lean_ctor_set(x_1265, 1, x_1264);
x_1266 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1266, 0, x_1202);
lean_ctor_set(x_1266, 1, x_1265);
lean_ctor_set(x_1266, 2, x_1203);
lean_ctor_set(x_1266, 3, x_1204);
lean_ctor_set(x_1266, 4, x_1205);
lean_ctor_set(x_1266, 5, x_1206);
lean_ctor_set(x_1266, 6, x_1207);
lean_ctor_set(x_1266, 7, x_1208);
lean_ctor_set(x_1266, 8, x_1209);
lean_ctor_set(x_1266, 9, x_1210);
lean_ctor_set(x_1266, 10, x_1211);
lean_ctor_set(x_1266, 11, x_1212);
x_1267 = lean_st_ref_set(x_3, x_1266, x_1201);
x_1268 = lean_ctor_get(x_1267, 1);
lean_inc(x_1268);
lean_dec(x_1267);
x_1149 = x_1196;
x_1150 = x_1268;
goto block_1173;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1269, 0, x_1255);
lean_ctor_set(x_1269, 1, x_1257);
x_1270 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1270, 0, x_1202);
lean_ctor_set(x_1270, 1, x_1269);
lean_ctor_set(x_1270, 2, x_1203);
lean_ctor_set(x_1270, 3, x_1204);
lean_ctor_set(x_1270, 4, x_1205);
lean_ctor_set(x_1270, 5, x_1206);
lean_ctor_set(x_1270, 6, x_1207);
lean_ctor_set(x_1270, 7, x_1208);
lean_ctor_set(x_1270, 8, x_1209);
lean_ctor_set(x_1270, 9, x_1210);
lean_ctor_set(x_1270, 10, x_1211);
lean_ctor_set(x_1270, 11, x_1212);
x_1271 = lean_st_ref_set(x_3, x_1270, x_1201);
x_1272 = lean_ctor_get(x_1271, 1);
lean_inc(x_1272);
lean_dec(x_1271);
x_1149 = x_1196;
x_1150 = x_1272;
goto block_1173;
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1273 = lean_box(0);
x_1274 = lean_array_uset(x_1247, x_1251, x_1273);
lean_inc(x_1196);
x_1275 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1146, x_1196, x_1252);
x_1276 = lean_array_uset(x_1274, x_1251, x_1275);
x_1277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1277, 0, x_1246);
lean_ctor_set(x_1277, 1, x_1276);
x_1278 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1278, 0, x_1202);
lean_ctor_set(x_1278, 1, x_1277);
lean_ctor_set(x_1278, 2, x_1203);
lean_ctor_set(x_1278, 3, x_1204);
lean_ctor_set(x_1278, 4, x_1205);
lean_ctor_set(x_1278, 5, x_1206);
lean_ctor_set(x_1278, 6, x_1207);
lean_ctor_set(x_1278, 7, x_1208);
lean_ctor_set(x_1278, 8, x_1209);
lean_ctor_set(x_1278, 9, x_1210);
lean_ctor_set(x_1278, 10, x_1211);
lean_ctor_set(x_1278, 11, x_1212);
x_1279 = lean_st_ref_set(x_3, x_1278, x_1201);
x_1280 = lean_ctor_get(x_1279, 1);
lean_inc(x_1280);
lean_dec(x_1279);
x_1149 = x_1196;
x_1150 = x_1280;
goto block_1173;
}
}
}
else
{
uint8_t x_1281; 
lean_dec(x_1147);
lean_dec(x_1146);
lean_dec(x_1);
x_1281 = !lean_is_exclusive(x_1195);
if (x_1281 == 0)
{
return x_1195;
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1195, 0);
x_1283 = lean_ctor_get(x_1195, 1);
lean_inc(x_1283);
lean_inc(x_1282);
lean_dec(x_1195);
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set(x_1284, 1, x_1283);
return x_1284;
}
}
}
else
{
lean_object* x_1285; 
lean_dec(x_1146);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1285 = lean_ctor_get(x_1194, 0);
lean_inc(x_1285);
lean_dec(x_1194);
x_1149 = x_1285;
x_1150 = x_1178;
goto block_1173;
}
}
}
block_1406:
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; uint64_t x_1301; uint64_t x_1302; uint64_t x_1303; uint64_t x_1304; uint64_t x_1305; uint64_t x_1306; uint64_t x_1307; size_t x_1308; size_t x_1309; size_t x_1310; size_t x_1311; size_t x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1294);
x_1295 = lean_st_ref_get(x_3, x_8);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1296, 1);
lean_inc(x_1297);
lean_dec(x_1296);
x_1298 = lean_ctor_get(x_1295, 1);
lean_inc(x_1298);
lean_dec(x_1295);
x_1299 = lean_ctor_get(x_1297, 1);
lean_inc(x_1299);
lean_dec(x_1297);
x_1300 = lean_array_get_size(x_1299);
x_1301 = l_Lean_Expr_hash(x_1145);
x_1302 = 32;
x_1303 = lean_uint64_shift_right(x_1301, x_1302);
x_1304 = lean_uint64_xor(x_1301, x_1303);
x_1305 = 16;
x_1306 = lean_uint64_shift_right(x_1304, x_1305);
x_1307 = lean_uint64_xor(x_1304, x_1306);
x_1308 = lean_uint64_to_usize(x_1307);
x_1309 = lean_usize_of_nat(x_1300);
lean_dec(x_1300);
x_1310 = 1;
x_1311 = lean_usize_sub(x_1309, x_1310);
x_1312 = lean_usize_land(x_1308, x_1311);
x_1313 = lean_array_uget(x_1299, x_1312);
lean_dec(x_1299);
x_1314 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1145, x_1313);
lean_dec(x_1313);
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1145);
x_1315 = l_Lean_Meta_Closure_collectExprAux(x_1145, x_2, x_3, x_4, x_5, x_6, x_7, x_1298);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; uint8_t x_1333; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
x_1318 = lean_st_ref_take(x_3, x_1317);
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1319, 1);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1318, 1);
lean_inc(x_1321);
lean_dec(x_1318);
x_1322 = lean_ctor_get(x_1319, 0);
lean_inc(x_1322);
x_1323 = lean_ctor_get(x_1319, 2);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1319, 3);
lean_inc(x_1324);
x_1325 = lean_ctor_get(x_1319, 4);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1319, 5);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_1319, 6);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1319, 7);
lean_inc(x_1328);
x_1329 = lean_ctor_get(x_1319, 8);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1319, 9);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1319, 10);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1319, 11);
lean_inc(x_1332);
lean_dec(x_1319);
x_1333 = !lean_is_exclusive(x_1320);
if (x_1333 == 0)
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; size_t x_1337; size_t x_1338; size_t x_1339; lean_object* x_1340; uint8_t x_1341; 
x_1334 = lean_ctor_get(x_1320, 0);
x_1335 = lean_ctor_get(x_1320, 1);
x_1336 = lean_array_get_size(x_1335);
x_1337 = lean_usize_of_nat(x_1336);
lean_dec(x_1336);
x_1338 = lean_usize_sub(x_1337, x_1310);
x_1339 = lean_usize_land(x_1308, x_1338);
x_1340 = lean_array_uget(x_1335, x_1339);
x_1341 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1145, x_1340);
if (x_1341 == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; uint8_t x_1351; 
x_1342 = lean_unsigned_to_nat(1u);
x_1343 = lean_nat_add(x_1334, x_1342);
lean_dec(x_1334);
lean_inc(x_1316);
x_1344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1344, 0, x_1145);
lean_ctor_set(x_1344, 1, x_1316);
lean_ctor_set(x_1344, 2, x_1340);
x_1345 = lean_array_uset(x_1335, x_1339, x_1344);
x_1346 = lean_unsigned_to_nat(4u);
x_1347 = lean_nat_mul(x_1343, x_1346);
x_1348 = lean_unsigned_to_nat(3u);
x_1349 = lean_nat_div(x_1347, x_1348);
lean_dec(x_1347);
x_1350 = lean_array_get_size(x_1345);
x_1351 = lean_nat_dec_le(x_1349, x_1350);
lean_dec(x_1350);
lean_dec(x_1349);
if (x_1351 == 0)
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1352 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1345);
lean_ctor_set(x_1320, 1, x_1352);
lean_ctor_set(x_1320, 0, x_1343);
x_1353 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1353, 0, x_1322);
lean_ctor_set(x_1353, 1, x_1320);
lean_ctor_set(x_1353, 2, x_1323);
lean_ctor_set(x_1353, 3, x_1324);
lean_ctor_set(x_1353, 4, x_1325);
lean_ctor_set(x_1353, 5, x_1326);
lean_ctor_set(x_1353, 6, x_1327);
lean_ctor_set(x_1353, 7, x_1328);
lean_ctor_set(x_1353, 8, x_1329);
lean_ctor_set(x_1353, 9, x_1330);
lean_ctor_set(x_1353, 10, x_1331);
lean_ctor_set(x_1353, 11, x_1332);
x_1354 = lean_st_ref_set(x_3, x_1353, x_1321);
x_1355 = lean_ctor_get(x_1354, 1);
lean_inc(x_1355);
lean_dec(x_1354);
x_1147 = x_1316;
x_1148 = x_1355;
goto block_1293;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
lean_ctor_set(x_1320, 1, x_1345);
lean_ctor_set(x_1320, 0, x_1343);
x_1356 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1356, 0, x_1322);
lean_ctor_set(x_1356, 1, x_1320);
lean_ctor_set(x_1356, 2, x_1323);
lean_ctor_set(x_1356, 3, x_1324);
lean_ctor_set(x_1356, 4, x_1325);
lean_ctor_set(x_1356, 5, x_1326);
lean_ctor_set(x_1356, 6, x_1327);
lean_ctor_set(x_1356, 7, x_1328);
lean_ctor_set(x_1356, 8, x_1329);
lean_ctor_set(x_1356, 9, x_1330);
lean_ctor_set(x_1356, 10, x_1331);
lean_ctor_set(x_1356, 11, x_1332);
x_1357 = lean_st_ref_set(x_3, x_1356, x_1321);
x_1358 = lean_ctor_get(x_1357, 1);
lean_inc(x_1358);
lean_dec(x_1357);
x_1147 = x_1316;
x_1148 = x_1358;
goto block_1293;
}
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1359 = lean_box(0);
x_1360 = lean_array_uset(x_1335, x_1339, x_1359);
lean_inc(x_1316);
x_1361 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1145, x_1316, x_1340);
x_1362 = lean_array_uset(x_1360, x_1339, x_1361);
lean_ctor_set(x_1320, 1, x_1362);
x_1363 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1363, 0, x_1322);
lean_ctor_set(x_1363, 1, x_1320);
lean_ctor_set(x_1363, 2, x_1323);
lean_ctor_set(x_1363, 3, x_1324);
lean_ctor_set(x_1363, 4, x_1325);
lean_ctor_set(x_1363, 5, x_1326);
lean_ctor_set(x_1363, 6, x_1327);
lean_ctor_set(x_1363, 7, x_1328);
lean_ctor_set(x_1363, 8, x_1329);
lean_ctor_set(x_1363, 9, x_1330);
lean_ctor_set(x_1363, 10, x_1331);
lean_ctor_set(x_1363, 11, x_1332);
x_1364 = lean_st_ref_set(x_3, x_1363, x_1321);
x_1365 = lean_ctor_get(x_1364, 1);
lean_inc(x_1365);
lean_dec(x_1364);
x_1147 = x_1316;
x_1148 = x_1365;
goto block_1293;
}
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; size_t x_1369; size_t x_1370; size_t x_1371; lean_object* x_1372; uint8_t x_1373; 
x_1366 = lean_ctor_get(x_1320, 0);
x_1367 = lean_ctor_get(x_1320, 1);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1320);
x_1368 = lean_array_get_size(x_1367);
x_1369 = lean_usize_of_nat(x_1368);
lean_dec(x_1368);
x_1370 = lean_usize_sub(x_1369, x_1310);
x_1371 = lean_usize_land(x_1308, x_1370);
x_1372 = lean_array_uget(x_1367, x_1371);
x_1373 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1145, x_1372);
if (x_1373 == 0)
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; 
x_1374 = lean_unsigned_to_nat(1u);
x_1375 = lean_nat_add(x_1366, x_1374);
lean_dec(x_1366);
lean_inc(x_1316);
x_1376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1376, 0, x_1145);
lean_ctor_set(x_1376, 1, x_1316);
lean_ctor_set(x_1376, 2, x_1372);
x_1377 = lean_array_uset(x_1367, x_1371, x_1376);
x_1378 = lean_unsigned_to_nat(4u);
x_1379 = lean_nat_mul(x_1375, x_1378);
x_1380 = lean_unsigned_to_nat(3u);
x_1381 = lean_nat_div(x_1379, x_1380);
lean_dec(x_1379);
x_1382 = lean_array_get_size(x_1377);
x_1383 = lean_nat_dec_le(x_1381, x_1382);
lean_dec(x_1382);
lean_dec(x_1381);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1384 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1377);
x_1385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1385, 0, x_1375);
lean_ctor_set(x_1385, 1, x_1384);
x_1386 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1386, 0, x_1322);
lean_ctor_set(x_1386, 1, x_1385);
lean_ctor_set(x_1386, 2, x_1323);
lean_ctor_set(x_1386, 3, x_1324);
lean_ctor_set(x_1386, 4, x_1325);
lean_ctor_set(x_1386, 5, x_1326);
lean_ctor_set(x_1386, 6, x_1327);
lean_ctor_set(x_1386, 7, x_1328);
lean_ctor_set(x_1386, 8, x_1329);
lean_ctor_set(x_1386, 9, x_1330);
lean_ctor_set(x_1386, 10, x_1331);
lean_ctor_set(x_1386, 11, x_1332);
x_1387 = lean_st_ref_set(x_3, x_1386, x_1321);
x_1388 = lean_ctor_get(x_1387, 1);
lean_inc(x_1388);
lean_dec(x_1387);
x_1147 = x_1316;
x_1148 = x_1388;
goto block_1293;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1389, 0, x_1375);
lean_ctor_set(x_1389, 1, x_1377);
x_1390 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1390, 0, x_1322);
lean_ctor_set(x_1390, 1, x_1389);
lean_ctor_set(x_1390, 2, x_1323);
lean_ctor_set(x_1390, 3, x_1324);
lean_ctor_set(x_1390, 4, x_1325);
lean_ctor_set(x_1390, 5, x_1326);
lean_ctor_set(x_1390, 6, x_1327);
lean_ctor_set(x_1390, 7, x_1328);
lean_ctor_set(x_1390, 8, x_1329);
lean_ctor_set(x_1390, 9, x_1330);
lean_ctor_set(x_1390, 10, x_1331);
lean_ctor_set(x_1390, 11, x_1332);
x_1391 = lean_st_ref_set(x_3, x_1390, x_1321);
x_1392 = lean_ctor_get(x_1391, 1);
lean_inc(x_1392);
lean_dec(x_1391);
x_1147 = x_1316;
x_1148 = x_1392;
goto block_1293;
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1393 = lean_box(0);
x_1394 = lean_array_uset(x_1367, x_1371, x_1393);
lean_inc(x_1316);
x_1395 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1145, x_1316, x_1372);
x_1396 = lean_array_uset(x_1394, x_1371, x_1395);
x_1397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1397, 0, x_1366);
lean_ctor_set(x_1397, 1, x_1396);
x_1398 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1398, 0, x_1322);
lean_ctor_set(x_1398, 1, x_1397);
lean_ctor_set(x_1398, 2, x_1323);
lean_ctor_set(x_1398, 3, x_1324);
lean_ctor_set(x_1398, 4, x_1325);
lean_ctor_set(x_1398, 5, x_1326);
lean_ctor_set(x_1398, 6, x_1327);
lean_ctor_set(x_1398, 7, x_1328);
lean_ctor_set(x_1398, 8, x_1329);
lean_ctor_set(x_1398, 9, x_1330);
lean_ctor_set(x_1398, 10, x_1331);
lean_ctor_set(x_1398, 11, x_1332);
x_1399 = lean_st_ref_set(x_3, x_1398, x_1321);
x_1400 = lean_ctor_get(x_1399, 1);
lean_inc(x_1400);
lean_dec(x_1399);
x_1147 = x_1316;
x_1148 = x_1400;
goto block_1293;
}
}
}
else
{
uint8_t x_1401; 
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1401 = !lean_is_exclusive(x_1315);
if (x_1401 == 0)
{
return x_1315;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
x_1402 = lean_ctor_get(x_1315, 0);
x_1403 = lean_ctor_get(x_1315, 1);
lean_inc(x_1403);
lean_inc(x_1402);
lean_dec(x_1315);
x_1404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1404, 0, x_1402);
lean_ctor_set(x_1404, 1, x_1403);
return x_1404;
}
}
}
else
{
lean_object* x_1405; 
lean_dec(x_1145);
x_1405 = lean_ctor_get(x_1314, 0);
lean_inc(x_1405);
lean_dec(x_1314);
x_1147 = x_1405;
x_1148 = x_1298;
goto block_1293;
}
}
}
case 8:
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1687; uint8_t x_1800; 
x_1413 = lean_ctor_get(x_1, 1);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1, 2);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_1, 3);
lean_inc(x_1415);
x_1800 = l_Lean_Expr_hasLevelParam(x_1413);
if (x_1800 == 0)
{
uint8_t x_1801; 
x_1801 = l_Lean_Expr_hasFVar(x_1413);
if (x_1801 == 0)
{
uint8_t x_1802; 
x_1802 = l_Lean_Expr_hasMVar(x_1413);
if (x_1802 == 0)
{
x_1416 = x_1413;
x_1417 = x_8;
goto block_1686;
}
else
{
lean_object* x_1803; 
x_1803 = lean_box(0);
x_1687 = x_1803;
goto block_1799;
}
}
else
{
lean_object* x_1804; 
x_1804 = lean_box(0);
x_1687 = x_1804;
goto block_1799;
}
}
else
{
lean_object* x_1805; 
x_1805 = lean_box(0);
x_1687 = x_1805;
goto block_1799;
}
block_1686:
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1567; uint8_t x_1680; 
x_1680 = l_Lean_Expr_hasLevelParam(x_1414);
if (x_1680 == 0)
{
uint8_t x_1681; 
x_1681 = l_Lean_Expr_hasFVar(x_1414);
if (x_1681 == 0)
{
uint8_t x_1682; 
x_1682 = l_Lean_Expr_hasMVar(x_1414);
if (x_1682 == 0)
{
x_1418 = x_1414;
x_1419 = x_1417;
goto block_1566;
}
else
{
lean_object* x_1683; 
x_1683 = lean_box(0);
x_1567 = x_1683;
goto block_1679;
}
}
else
{
lean_object* x_1684; 
x_1684 = lean_box(0);
x_1567 = x_1684;
goto block_1679;
}
}
else
{
lean_object* x_1685; 
x_1685 = lean_box(0);
x_1567 = x_1685;
goto block_1679;
}
block_1566:
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1447; uint8_t x_1560; 
x_1560 = l_Lean_Expr_hasLevelParam(x_1415);
if (x_1560 == 0)
{
uint8_t x_1561; 
x_1561 = l_Lean_Expr_hasFVar(x_1415);
if (x_1561 == 0)
{
uint8_t x_1562; 
x_1562 = l_Lean_Expr_hasMVar(x_1415);
if (x_1562 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1420 = x_1415;
x_1421 = x_1419;
goto block_1446;
}
else
{
lean_object* x_1563; 
x_1563 = lean_box(0);
x_1447 = x_1563;
goto block_1559;
}
}
else
{
lean_object* x_1564; 
x_1564 = lean_box(0);
x_1447 = x_1564;
goto block_1559;
}
}
else
{
lean_object* x_1565; 
x_1565 = lean_box(0);
x_1447 = x_1565;
goto block_1559;
}
block_1446:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; uint8_t x_1426; size_t x_1427; size_t x_1428; uint8_t x_1429; 
x_1422 = lean_ctor_get(x_1, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1, 1);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1, 2);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1, 3);
lean_inc(x_1425);
x_1426 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_1427 = lean_ptr_addr(x_1423);
lean_dec(x_1423);
x_1428 = lean_ptr_addr(x_1416);
x_1429 = lean_usize_dec_eq(x_1427, x_1428);
if (x_1429 == 0)
{
lean_object* x_1430; lean_object* x_1431; 
lean_dec(x_1425);
lean_dec(x_1424);
lean_dec(x_1);
x_1430 = l_Lean_Expr_letE___override(x_1422, x_1416, x_1418, x_1420, x_1426);
x_1431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1431, 0, x_1430);
lean_ctor_set(x_1431, 1, x_1421);
return x_1431;
}
else
{
size_t x_1432; size_t x_1433; uint8_t x_1434; 
x_1432 = lean_ptr_addr(x_1424);
lean_dec(x_1424);
x_1433 = lean_ptr_addr(x_1418);
x_1434 = lean_usize_dec_eq(x_1432, x_1433);
if (x_1434 == 0)
{
lean_object* x_1435; lean_object* x_1436; 
lean_dec(x_1425);
lean_dec(x_1);
x_1435 = l_Lean_Expr_letE___override(x_1422, x_1416, x_1418, x_1420, x_1426);
x_1436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1436, 0, x_1435);
lean_ctor_set(x_1436, 1, x_1421);
return x_1436;
}
else
{
size_t x_1437; size_t x_1438; uint8_t x_1439; 
x_1437 = lean_ptr_addr(x_1425);
lean_dec(x_1425);
x_1438 = lean_ptr_addr(x_1420);
x_1439 = lean_usize_dec_eq(x_1437, x_1438);
if (x_1439 == 0)
{
lean_object* x_1440; lean_object* x_1441; 
lean_dec(x_1);
x_1440 = l_Lean_Expr_letE___override(x_1422, x_1416, x_1418, x_1420, x_1426);
x_1441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1441, 0, x_1440);
lean_ctor_set(x_1441, 1, x_1421);
return x_1441;
}
else
{
lean_object* x_1442; 
lean_dec(x_1422);
lean_dec(x_1420);
lean_dec(x_1418);
lean_dec(x_1416);
x_1442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1442, 0, x_1);
lean_ctor_set(x_1442, 1, x_1421);
return x_1442;
}
}
}
}
else
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
lean_dec(x_1420);
lean_dec(x_1418);
lean_dec(x_1416);
lean_dec(x_1);
x_1443 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_1444 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_1443);
x_1445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1445, 0, x_1444);
lean_ctor_set(x_1445, 1, x_1421);
return x_1445;
}
}
block_1559:
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; uint64_t x_1454; uint64_t x_1455; uint64_t x_1456; uint64_t x_1457; uint64_t x_1458; uint64_t x_1459; uint64_t x_1460; size_t x_1461; size_t x_1462; size_t x_1463; size_t x_1464; size_t x_1465; lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1447);
x_1448 = lean_st_ref_get(x_3, x_1419);
x_1449 = lean_ctor_get(x_1448, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1449, 1);
lean_inc(x_1450);
lean_dec(x_1449);
x_1451 = lean_ctor_get(x_1448, 1);
lean_inc(x_1451);
lean_dec(x_1448);
x_1452 = lean_ctor_get(x_1450, 1);
lean_inc(x_1452);
lean_dec(x_1450);
x_1453 = lean_array_get_size(x_1452);
x_1454 = l_Lean_Expr_hash(x_1415);
x_1455 = 32;
x_1456 = lean_uint64_shift_right(x_1454, x_1455);
x_1457 = lean_uint64_xor(x_1454, x_1456);
x_1458 = 16;
x_1459 = lean_uint64_shift_right(x_1457, x_1458);
x_1460 = lean_uint64_xor(x_1457, x_1459);
x_1461 = lean_uint64_to_usize(x_1460);
x_1462 = lean_usize_of_nat(x_1453);
lean_dec(x_1453);
x_1463 = 1;
x_1464 = lean_usize_sub(x_1462, x_1463);
x_1465 = lean_usize_land(x_1461, x_1464);
x_1466 = lean_array_uget(x_1452, x_1465);
lean_dec(x_1452);
x_1467 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1415, x_1466);
lean_dec(x_1466);
if (lean_obj_tag(x_1467) == 0)
{
lean_object* x_1468; 
lean_inc(x_1415);
x_1468 = l_Lean_Meta_Closure_collectExprAux(x_1415, x_2, x_3, x_4, x_5, x_6, x_7, x_1451);
if (lean_obj_tag(x_1468) == 0)
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; 
x_1469 = lean_ctor_get(x_1468, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1468, 1);
lean_inc(x_1470);
lean_dec(x_1468);
x_1471 = lean_st_ref_take(x_3, x_1470);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1472, 1);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1471, 1);
lean_inc(x_1474);
lean_dec(x_1471);
x_1475 = lean_ctor_get(x_1472, 0);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_1472, 2);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1472, 3);
lean_inc(x_1477);
x_1478 = lean_ctor_get(x_1472, 4);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1472, 5);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1472, 6);
lean_inc(x_1480);
x_1481 = lean_ctor_get(x_1472, 7);
lean_inc(x_1481);
x_1482 = lean_ctor_get(x_1472, 8);
lean_inc(x_1482);
x_1483 = lean_ctor_get(x_1472, 9);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1472, 10);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1472, 11);
lean_inc(x_1485);
lean_dec(x_1472);
x_1486 = !lean_is_exclusive(x_1473);
if (x_1486 == 0)
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; size_t x_1490; size_t x_1491; size_t x_1492; lean_object* x_1493; uint8_t x_1494; 
x_1487 = lean_ctor_get(x_1473, 0);
x_1488 = lean_ctor_get(x_1473, 1);
x_1489 = lean_array_get_size(x_1488);
x_1490 = lean_usize_of_nat(x_1489);
lean_dec(x_1489);
x_1491 = lean_usize_sub(x_1490, x_1463);
x_1492 = lean_usize_land(x_1461, x_1491);
x_1493 = lean_array_uget(x_1488, x_1492);
x_1494 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1415, x_1493);
if (x_1494 == 0)
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; uint8_t x_1504; 
x_1495 = lean_unsigned_to_nat(1u);
x_1496 = lean_nat_add(x_1487, x_1495);
lean_dec(x_1487);
lean_inc(x_1469);
x_1497 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1497, 0, x_1415);
lean_ctor_set(x_1497, 1, x_1469);
lean_ctor_set(x_1497, 2, x_1493);
x_1498 = lean_array_uset(x_1488, x_1492, x_1497);
x_1499 = lean_unsigned_to_nat(4u);
x_1500 = lean_nat_mul(x_1496, x_1499);
x_1501 = lean_unsigned_to_nat(3u);
x_1502 = lean_nat_div(x_1500, x_1501);
lean_dec(x_1500);
x_1503 = lean_array_get_size(x_1498);
x_1504 = lean_nat_dec_le(x_1502, x_1503);
lean_dec(x_1503);
lean_dec(x_1502);
if (x_1504 == 0)
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1505 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1498);
lean_ctor_set(x_1473, 1, x_1505);
lean_ctor_set(x_1473, 0, x_1496);
x_1506 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1506, 0, x_1475);
lean_ctor_set(x_1506, 1, x_1473);
lean_ctor_set(x_1506, 2, x_1476);
lean_ctor_set(x_1506, 3, x_1477);
lean_ctor_set(x_1506, 4, x_1478);
lean_ctor_set(x_1506, 5, x_1479);
lean_ctor_set(x_1506, 6, x_1480);
lean_ctor_set(x_1506, 7, x_1481);
lean_ctor_set(x_1506, 8, x_1482);
lean_ctor_set(x_1506, 9, x_1483);
lean_ctor_set(x_1506, 10, x_1484);
lean_ctor_set(x_1506, 11, x_1485);
x_1507 = lean_st_ref_set(x_3, x_1506, x_1474);
x_1508 = lean_ctor_get(x_1507, 1);
lean_inc(x_1508);
lean_dec(x_1507);
x_1420 = x_1469;
x_1421 = x_1508;
goto block_1446;
}
else
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
lean_ctor_set(x_1473, 1, x_1498);
lean_ctor_set(x_1473, 0, x_1496);
x_1509 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1509, 0, x_1475);
lean_ctor_set(x_1509, 1, x_1473);
lean_ctor_set(x_1509, 2, x_1476);
lean_ctor_set(x_1509, 3, x_1477);
lean_ctor_set(x_1509, 4, x_1478);
lean_ctor_set(x_1509, 5, x_1479);
lean_ctor_set(x_1509, 6, x_1480);
lean_ctor_set(x_1509, 7, x_1481);
lean_ctor_set(x_1509, 8, x_1482);
lean_ctor_set(x_1509, 9, x_1483);
lean_ctor_set(x_1509, 10, x_1484);
lean_ctor_set(x_1509, 11, x_1485);
x_1510 = lean_st_ref_set(x_3, x_1509, x_1474);
x_1511 = lean_ctor_get(x_1510, 1);
lean_inc(x_1511);
lean_dec(x_1510);
x_1420 = x_1469;
x_1421 = x_1511;
goto block_1446;
}
}
else
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1512 = lean_box(0);
x_1513 = lean_array_uset(x_1488, x_1492, x_1512);
lean_inc(x_1469);
x_1514 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1415, x_1469, x_1493);
x_1515 = lean_array_uset(x_1513, x_1492, x_1514);
lean_ctor_set(x_1473, 1, x_1515);
x_1516 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1516, 0, x_1475);
lean_ctor_set(x_1516, 1, x_1473);
lean_ctor_set(x_1516, 2, x_1476);
lean_ctor_set(x_1516, 3, x_1477);
lean_ctor_set(x_1516, 4, x_1478);
lean_ctor_set(x_1516, 5, x_1479);
lean_ctor_set(x_1516, 6, x_1480);
lean_ctor_set(x_1516, 7, x_1481);
lean_ctor_set(x_1516, 8, x_1482);
lean_ctor_set(x_1516, 9, x_1483);
lean_ctor_set(x_1516, 10, x_1484);
lean_ctor_set(x_1516, 11, x_1485);
x_1517 = lean_st_ref_set(x_3, x_1516, x_1474);
x_1518 = lean_ctor_get(x_1517, 1);
lean_inc(x_1518);
lean_dec(x_1517);
x_1420 = x_1469;
x_1421 = x_1518;
goto block_1446;
}
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; size_t x_1522; size_t x_1523; size_t x_1524; lean_object* x_1525; uint8_t x_1526; 
x_1519 = lean_ctor_get(x_1473, 0);
x_1520 = lean_ctor_get(x_1473, 1);
lean_inc(x_1520);
lean_inc(x_1519);
lean_dec(x_1473);
x_1521 = lean_array_get_size(x_1520);
x_1522 = lean_usize_of_nat(x_1521);
lean_dec(x_1521);
x_1523 = lean_usize_sub(x_1522, x_1463);
x_1524 = lean_usize_land(x_1461, x_1523);
x_1525 = lean_array_uget(x_1520, x_1524);
x_1526 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1415, x_1525);
if (x_1526 == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; 
x_1527 = lean_unsigned_to_nat(1u);
x_1528 = lean_nat_add(x_1519, x_1527);
lean_dec(x_1519);
lean_inc(x_1469);
x_1529 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1529, 0, x_1415);
lean_ctor_set(x_1529, 1, x_1469);
lean_ctor_set(x_1529, 2, x_1525);
x_1530 = lean_array_uset(x_1520, x_1524, x_1529);
x_1531 = lean_unsigned_to_nat(4u);
x_1532 = lean_nat_mul(x_1528, x_1531);
x_1533 = lean_unsigned_to_nat(3u);
x_1534 = lean_nat_div(x_1532, x_1533);
lean_dec(x_1532);
x_1535 = lean_array_get_size(x_1530);
x_1536 = lean_nat_dec_le(x_1534, x_1535);
lean_dec(x_1535);
lean_dec(x_1534);
if (x_1536 == 0)
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
x_1537 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1530);
x_1538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1538, 0, x_1528);
lean_ctor_set(x_1538, 1, x_1537);
x_1539 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1539, 0, x_1475);
lean_ctor_set(x_1539, 1, x_1538);
lean_ctor_set(x_1539, 2, x_1476);
lean_ctor_set(x_1539, 3, x_1477);
lean_ctor_set(x_1539, 4, x_1478);
lean_ctor_set(x_1539, 5, x_1479);
lean_ctor_set(x_1539, 6, x_1480);
lean_ctor_set(x_1539, 7, x_1481);
lean_ctor_set(x_1539, 8, x_1482);
lean_ctor_set(x_1539, 9, x_1483);
lean_ctor_set(x_1539, 10, x_1484);
lean_ctor_set(x_1539, 11, x_1485);
x_1540 = lean_st_ref_set(x_3, x_1539, x_1474);
x_1541 = lean_ctor_get(x_1540, 1);
lean_inc(x_1541);
lean_dec(x_1540);
x_1420 = x_1469;
x_1421 = x_1541;
goto block_1446;
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; 
x_1542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1542, 0, x_1528);
lean_ctor_set(x_1542, 1, x_1530);
x_1543 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1543, 0, x_1475);
lean_ctor_set(x_1543, 1, x_1542);
lean_ctor_set(x_1543, 2, x_1476);
lean_ctor_set(x_1543, 3, x_1477);
lean_ctor_set(x_1543, 4, x_1478);
lean_ctor_set(x_1543, 5, x_1479);
lean_ctor_set(x_1543, 6, x_1480);
lean_ctor_set(x_1543, 7, x_1481);
lean_ctor_set(x_1543, 8, x_1482);
lean_ctor_set(x_1543, 9, x_1483);
lean_ctor_set(x_1543, 10, x_1484);
lean_ctor_set(x_1543, 11, x_1485);
x_1544 = lean_st_ref_set(x_3, x_1543, x_1474);
x_1545 = lean_ctor_get(x_1544, 1);
lean_inc(x_1545);
lean_dec(x_1544);
x_1420 = x_1469;
x_1421 = x_1545;
goto block_1446;
}
}
else
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
x_1546 = lean_box(0);
x_1547 = lean_array_uset(x_1520, x_1524, x_1546);
lean_inc(x_1469);
x_1548 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1415, x_1469, x_1525);
x_1549 = lean_array_uset(x_1547, x_1524, x_1548);
x_1550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1550, 0, x_1519);
lean_ctor_set(x_1550, 1, x_1549);
x_1551 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1551, 0, x_1475);
lean_ctor_set(x_1551, 1, x_1550);
lean_ctor_set(x_1551, 2, x_1476);
lean_ctor_set(x_1551, 3, x_1477);
lean_ctor_set(x_1551, 4, x_1478);
lean_ctor_set(x_1551, 5, x_1479);
lean_ctor_set(x_1551, 6, x_1480);
lean_ctor_set(x_1551, 7, x_1481);
lean_ctor_set(x_1551, 8, x_1482);
lean_ctor_set(x_1551, 9, x_1483);
lean_ctor_set(x_1551, 10, x_1484);
lean_ctor_set(x_1551, 11, x_1485);
x_1552 = lean_st_ref_set(x_3, x_1551, x_1474);
x_1553 = lean_ctor_get(x_1552, 1);
lean_inc(x_1553);
lean_dec(x_1552);
x_1420 = x_1469;
x_1421 = x_1553;
goto block_1446;
}
}
}
else
{
uint8_t x_1554; 
lean_dec(x_1418);
lean_dec(x_1416);
lean_dec(x_1415);
lean_dec(x_1);
x_1554 = !lean_is_exclusive(x_1468);
if (x_1554 == 0)
{
return x_1468;
}
else
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; 
x_1555 = lean_ctor_get(x_1468, 0);
x_1556 = lean_ctor_get(x_1468, 1);
lean_inc(x_1556);
lean_inc(x_1555);
lean_dec(x_1468);
x_1557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1557, 0, x_1555);
lean_ctor_set(x_1557, 1, x_1556);
return x_1557;
}
}
}
else
{
lean_object* x_1558; 
lean_dec(x_1415);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1558 = lean_ctor_get(x_1467, 0);
lean_inc(x_1558);
lean_dec(x_1467);
x_1420 = x_1558;
x_1421 = x_1451;
goto block_1446;
}
}
}
block_1679:
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; uint64_t x_1574; uint64_t x_1575; uint64_t x_1576; uint64_t x_1577; uint64_t x_1578; uint64_t x_1579; uint64_t x_1580; size_t x_1581; size_t x_1582; size_t x_1583; size_t x_1584; size_t x_1585; lean_object* x_1586; lean_object* x_1587; 
lean_dec(x_1567);
x_1568 = lean_st_ref_get(x_3, x_1417);
x_1569 = lean_ctor_get(x_1568, 0);
lean_inc(x_1569);
x_1570 = lean_ctor_get(x_1569, 1);
lean_inc(x_1570);
lean_dec(x_1569);
x_1571 = lean_ctor_get(x_1568, 1);
lean_inc(x_1571);
lean_dec(x_1568);
x_1572 = lean_ctor_get(x_1570, 1);
lean_inc(x_1572);
lean_dec(x_1570);
x_1573 = lean_array_get_size(x_1572);
x_1574 = l_Lean_Expr_hash(x_1414);
x_1575 = 32;
x_1576 = lean_uint64_shift_right(x_1574, x_1575);
x_1577 = lean_uint64_xor(x_1574, x_1576);
x_1578 = 16;
x_1579 = lean_uint64_shift_right(x_1577, x_1578);
x_1580 = lean_uint64_xor(x_1577, x_1579);
x_1581 = lean_uint64_to_usize(x_1580);
x_1582 = lean_usize_of_nat(x_1573);
lean_dec(x_1573);
x_1583 = 1;
x_1584 = lean_usize_sub(x_1582, x_1583);
x_1585 = lean_usize_land(x_1581, x_1584);
x_1586 = lean_array_uget(x_1572, x_1585);
lean_dec(x_1572);
x_1587 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1414, x_1586);
lean_dec(x_1586);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1414);
x_1588 = l_Lean_Meta_Closure_collectExprAux(x_1414, x_2, x_3, x_4, x_5, x_6, x_7, x_1571);
if (lean_obj_tag(x_1588) == 0)
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; uint8_t x_1606; 
x_1589 = lean_ctor_get(x_1588, 0);
lean_inc(x_1589);
x_1590 = lean_ctor_get(x_1588, 1);
lean_inc(x_1590);
lean_dec(x_1588);
x_1591 = lean_st_ref_take(x_3, x_1590);
x_1592 = lean_ctor_get(x_1591, 0);
lean_inc(x_1592);
x_1593 = lean_ctor_get(x_1592, 1);
lean_inc(x_1593);
x_1594 = lean_ctor_get(x_1591, 1);
lean_inc(x_1594);
lean_dec(x_1591);
x_1595 = lean_ctor_get(x_1592, 0);
lean_inc(x_1595);
x_1596 = lean_ctor_get(x_1592, 2);
lean_inc(x_1596);
x_1597 = lean_ctor_get(x_1592, 3);
lean_inc(x_1597);
x_1598 = lean_ctor_get(x_1592, 4);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1592, 5);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1592, 6);
lean_inc(x_1600);
x_1601 = lean_ctor_get(x_1592, 7);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1592, 8);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1592, 9);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1592, 10);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1592, 11);
lean_inc(x_1605);
lean_dec(x_1592);
x_1606 = !lean_is_exclusive(x_1593);
if (x_1606 == 0)
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; size_t x_1610; size_t x_1611; size_t x_1612; lean_object* x_1613; uint8_t x_1614; 
x_1607 = lean_ctor_get(x_1593, 0);
x_1608 = lean_ctor_get(x_1593, 1);
x_1609 = lean_array_get_size(x_1608);
x_1610 = lean_usize_of_nat(x_1609);
lean_dec(x_1609);
x_1611 = lean_usize_sub(x_1610, x_1583);
x_1612 = lean_usize_land(x_1581, x_1611);
x_1613 = lean_array_uget(x_1608, x_1612);
x_1614 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1414, x_1613);
if (x_1614 == 0)
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; uint8_t x_1624; 
x_1615 = lean_unsigned_to_nat(1u);
x_1616 = lean_nat_add(x_1607, x_1615);
lean_dec(x_1607);
lean_inc(x_1589);
x_1617 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1617, 0, x_1414);
lean_ctor_set(x_1617, 1, x_1589);
lean_ctor_set(x_1617, 2, x_1613);
x_1618 = lean_array_uset(x_1608, x_1612, x_1617);
x_1619 = lean_unsigned_to_nat(4u);
x_1620 = lean_nat_mul(x_1616, x_1619);
x_1621 = lean_unsigned_to_nat(3u);
x_1622 = lean_nat_div(x_1620, x_1621);
lean_dec(x_1620);
x_1623 = lean_array_get_size(x_1618);
x_1624 = lean_nat_dec_le(x_1622, x_1623);
lean_dec(x_1623);
lean_dec(x_1622);
if (x_1624 == 0)
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; 
x_1625 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1618);
lean_ctor_set(x_1593, 1, x_1625);
lean_ctor_set(x_1593, 0, x_1616);
x_1626 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1626, 0, x_1595);
lean_ctor_set(x_1626, 1, x_1593);
lean_ctor_set(x_1626, 2, x_1596);
lean_ctor_set(x_1626, 3, x_1597);
lean_ctor_set(x_1626, 4, x_1598);
lean_ctor_set(x_1626, 5, x_1599);
lean_ctor_set(x_1626, 6, x_1600);
lean_ctor_set(x_1626, 7, x_1601);
lean_ctor_set(x_1626, 8, x_1602);
lean_ctor_set(x_1626, 9, x_1603);
lean_ctor_set(x_1626, 10, x_1604);
lean_ctor_set(x_1626, 11, x_1605);
x_1627 = lean_st_ref_set(x_3, x_1626, x_1594);
x_1628 = lean_ctor_get(x_1627, 1);
lean_inc(x_1628);
lean_dec(x_1627);
x_1418 = x_1589;
x_1419 = x_1628;
goto block_1566;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_ctor_set(x_1593, 1, x_1618);
lean_ctor_set(x_1593, 0, x_1616);
x_1629 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1629, 0, x_1595);
lean_ctor_set(x_1629, 1, x_1593);
lean_ctor_set(x_1629, 2, x_1596);
lean_ctor_set(x_1629, 3, x_1597);
lean_ctor_set(x_1629, 4, x_1598);
lean_ctor_set(x_1629, 5, x_1599);
lean_ctor_set(x_1629, 6, x_1600);
lean_ctor_set(x_1629, 7, x_1601);
lean_ctor_set(x_1629, 8, x_1602);
lean_ctor_set(x_1629, 9, x_1603);
lean_ctor_set(x_1629, 10, x_1604);
lean_ctor_set(x_1629, 11, x_1605);
x_1630 = lean_st_ref_set(x_3, x_1629, x_1594);
x_1631 = lean_ctor_get(x_1630, 1);
lean_inc(x_1631);
lean_dec(x_1630);
x_1418 = x_1589;
x_1419 = x_1631;
goto block_1566;
}
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
x_1632 = lean_box(0);
x_1633 = lean_array_uset(x_1608, x_1612, x_1632);
lean_inc(x_1589);
x_1634 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1414, x_1589, x_1613);
x_1635 = lean_array_uset(x_1633, x_1612, x_1634);
lean_ctor_set(x_1593, 1, x_1635);
x_1636 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1636, 0, x_1595);
lean_ctor_set(x_1636, 1, x_1593);
lean_ctor_set(x_1636, 2, x_1596);
lean_ctor_set(x_1636, 3, x_1597);
lean_ctor_set(x_1636, 4, x_1598);
lean_ctor_set(x_1636, 5, x_1599);
lean_ctor_set(x_1636, 6, x_1600);
lean_ctor_set(x_1636, 7, x_1601);
lean_ctor_set(x_1636, 8, x_1602);
lean_ctor_set(x_1636, 9, x_1603);
lean_ctor_set(x_1636, 10, x_1604);
lean_ctor_set(x_1636, 11, x_1605);
x_1637 = lean_st_ref_set(x_3, x_1636, x_1594);
x_1638 = lean_ctor_get(x_1637, 1);
lean_inc(x_1638);
lean_dec(x_1637);
x_1418 = x_1589;
x_1419 = x_1638;
goto block_1566;
}
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; size_t x_1642; size_t x_1643; size_t x_1644; lean_object* x_1645; uint8_t x_1646; 
x_1639 = lean_ctor_get(x_1593, 0);
x_1640 = lean_ctor_get(x_1593, 1);
lean_inc(x_1640);
lean_inc(x_1639);
lean_dec(x_1593);
x_1641 = lean_array_get_size(x_1640);
x_1642 = lean_usize_of_nat(x_1641);
lean_dec(x_1641);
x_1643 = lean_usize_sub(x_1642, x_1583);
x_1644 = lean_usize_land(x_1581, x_1643);
x_1645 = lean_array_uget(x_1640, x_1644);
x_1646 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1414, x_1645);
if (x_1646 == 0)
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; uint8_t x_1656; 
x_1647 = lean_unsigned_to_nat(1u);
x_1648 = lean_nat_add(x_1639, x_1647);
lean_dec(x_1639);
lean_inc(x_1589);
x_1649 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1649, 0, x_1414);
lean_ctor_set(x_1649, 1, x_1589);
lean_ctor_set(x_1649, 2, x_1645);
x_1650 = lean_array_uset(x_1640, x_1644, x_1649);
x_1651 = lean_unsigned_to_nat(4u);
x_1652 = lean_nat_mul(x_1648, x_1651);
x_1653 = lean_unsigned_to_nat(3u);
x_1654 = lean_nat_div(x_1652, x_1653);
lean_dec(x_1652);
x_1655 = lean_array_get_size(x_1650);
x_1656 = lean_nat_dec_le(x_1654, x_1655);
lean_dec(x_1655);
lean_dec(x_1654);
if (x_1656 == 0)
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; 
x_1657 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1650);
x_1658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1658, 0, x_1648);
lean_ctor_set(x_1658, 1, x_1657);
x_1659 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1659, 0, x_1595);
lean_ctor_set(x_1659, 1, x_1658);
lean_ctor_set(x_1659, 2, x_1596);
lean_ctor_set(x_1659, 3, x_1597);
lean_ctor_set(x_1659, 4, x_1598);
lean_ctor_set(x_1659, 5, x_1599);
lean_ctor_set(x_1659, 6, x_1600);
lean_ctor_set(x_1659, 7, x_1601);
lean_ctor_set(x_1659, 8, x_1602);
lean_ctor_set(x_1659, 9, x_1603);
lean_ctor_set(x_1659, 10, x_1604);
lean_ctor_set(x_1659, 11, x_1605);
x_1660 = lean_st_ref_set(x_3, x_1659, x_1594);
x_1661 = lean_ctor_get(x_1660, 1);
lean_inc(x_1661);
lean_dec(x_1660);
x_1418 = x_1589;
x_1419 = x_1661;
goto block_1566;
}
else
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; 
x_1662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1662, 0, x_1648);
lean_ctor_set(x_1662, 1, x_1650);
x_1663 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1663, 0, x_1595);
lean_ctor_set(x_1663, 1, x_1662);
lean_ctor_set(x_1663, 2, x_1596);
lean_ctor_set(x_1663, 3, x_1597);
lean_ctor_set(x_1663, 4, x_1598);
lean_ctor_set(x_1663, 5, x_1599);
lean_ctor_set(x_1663, 6, x_1600);
lean_ctor_set(x_1663, 7, x_1601);
lean_ctor_set(x_1663, 8, x_1602);
lean_ctor_set(x_1663, 9, x_1603);
lean_ctor_set(x_1663, 10, x_1604);
lean_ctor_set(x_1663, 11, x_1605);
x_1664 = lean_st_ref_set(x_3, x_1663, x_1594);
x_1665 = lean_ctor_get(x_1664, 1);
lean_inc(x_1665);
lean_dec(x_1664);
x_1418 = x_1589;
x_1419 = x_1665;
goto block_1566;
}
}
else
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1666 = lean_box(0);
x_1667 = lean_array_uset(x_1640, x_1644, x_1666);
lean_inc(x_1589);
x_1668 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1414, x_1589, x_1645);
x_1669 = lean_array_uset(x_1667, x_1644, x_1668);
x_1670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1670, 0, x_1639);
lean_ctor_set(x_1670, 1, x_1669);
x_1671 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1671, 0, x_1595);
lean_ctor_set(x_1671, 1, x_1670);
lean_ctor_set(x_1671, 2, x_1596);
lean_ctor_set(x_1671, 3, x_1597);
lean_ctor_set(x_1671, 4, x_1598);
lean_ctor_set(x_1671, 5, x_1599);
lean_ctor_set(x_1671, 6, x_1600);
lean_ctor_set(x_1671, 7, x_1601);
lean_ctor_set(x_1671, 8, x_1602);
lean_ctor_set(x_1671, 9, x_1603);
lean_ctor_set(x_1671, 10, x_1604);
lean_ctor_set(x_1671, 11, x_1605);
x_1672 = lean_st_ref_set(x_3, x_1671, x_1594);
x_1673 = lean_ctor_get(x_1672, 1);
lean_inc(x_1673);
lean_dec(x_1672);
x_1418 = x_1589;
x_1419 = x_1673;
goto block_1566;
}
}
}
else
{
uint8_t x_1674; 
lean_dec(x_1416);
lean_dec(x_1415);
lean_dec(x_1414);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1674 = !lean_is_exclusive(x_1588);
if (x_1674 == 0)
{
return x_1588;
}
else
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
x_1675 = lean_ctor_get(x_1588, 0);
x_1676 = lean_ctor_get(x_1588, 1);
lean_inc(x_1676);
lean_inc(x_1675);
lean_dec(x_1588);
x_1677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set(x_1677, 1, x_1676);
return x_1677;
}
}
}
else
{
lean_object* x_1678; 
lean_dec(x_1414);
x_1678 = lean_ctor_get(x_1587, 0);
lean_inc(x_1678);
lean_dec(x_1587);
x_1418 = x_1678;
x_1419 = x_1571;
goto block_1566;
}
}
}
block_1799:
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; uint64_t x_1694; uint64_t x_1695; uint64_t x_1696; uint64_t x_1697; uint64_t x_1698; uint64_t x_1699; uint64_t x_1700; size_t x_1701; size_t x_1702; size_t x_1703; size_t x_1704; size_t x_1705; lean_object* x_1706; lean_object* x_1707; 
lean_dec(x_1687);
x_1688 = lean_st_ref_get(x_3, x_8);
x_1689 = lean_ctor_get(x_1688, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1689, 1);
lean_inc(x_1690);
lean_dec(x_1689);
x_1691 = lean_ctor_get(x_1688, 1);
lean_inc(x_1691);
lean_dec(x_1688);
x_1692 = lean_ctor_get(x_1690, 1);
lean_inc(x_1692);
lean_dec(x_1690);
x_1693 = lean_array_get_size(x_1692);
x_1694 = l_Lean_Expr_hash(x_1413);
x_1695 = 32;
x_1696 = lean_uint64_shift_right(x_1694, x_1695);
x_1697 = lean_uint64_xor(x_1694, x_1696);
x_1698 = 16;
x_1699 = lean_uint64_shift_right(x_1697, x_1698);
x_1700 = lean_uint64_xor(x_1697, x_1699);
x_1701 = lean_uint64_to_usize(x_1700);
x_1702 = lean_usize_of_nat(x_1693);
lean_dec(x_1693);
x_1703 = 1;
x_1704 = lean_usize_sub(x_1702, x_1703);
x_1705 = lean_usize_land(x_1701, x_1704);
x_1706 = lean_array_uget(x_1692, x_1705);
lean_dec(x_1692);
x_1707 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1413, x_1706);
lean_dec(x_1706);
if (lean_obj_tag(x_1707) == 0)
{
lean_object* x_1708; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1413);
x_1708 = l_Lean_Meta_Closure_collectExprAux(x_1413, x_2, x_3, x_4, x_5, x_6, x_7, x_1691);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; uint8_t x_1726; 
x_1709 = lean_ctor_get(x_1708, 0);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1708, 1);
lean_inc(x_1710);
lean_dec(x_1708);
x_1711 = lean_st_ref_take(x_3, x_1710);
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1712, 1);
lean_inc(x_1713);
x_1714 = lean_ctor_get(x_1711, 1);
lean_inc(x_1714);
lean_dec(x_1711);
x_1715 = lean_ctor_get(x_1712, 0);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1712, 2);
lean_inc(x_1716);
x_1717 = lean_ctor_get(x_1712, 3);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_1712, 4);
lean_inc(x_1718);
x_1719 = lean_ctor_get(x_1712, 5);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1712, 6);
lean_inc(x_1720);
x_1721 = lean_ctor_get(x_1712, 7);
lean_inc(x_1721);
x_1722 = lean_ctor_get(x_1712, 8);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_1712, 9);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1712, 10);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1712, 11);
lean_inc(x_1725);
lean_dec(x_1712);
x_1726 = !lean_is_exclusive(x_1713);
if (x_1726 == 0)
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; size_t x_1730; size_t x_1731; size_t x_1732; lean_object* x_1733; uint8_t x_1734; 
x_1727 = lean_ctor_get(x_1713, 0);
x_1728 = lean_ctor_get(x_1713, 1);
x_1729 = lean_array_get_size(x_1728);
x_1730 = lean_usize_of_nat(x_1729);
lean_dec(x_1729);
x_1731 = lean_usize_sub(x_1730, x_1703);
x_1732 = lean_usize_land(x_1701, x_1731);
x_1733 = lean_array_uget(x_1728, x_1732);
x_1734 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1413, x_1733);
if (x_1734 == 0)
{
lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; uint8_t x_1744; 
x_1735 = lean_unsigned_to_nat(1u);
x_1736 = lean_nat_add(x_1727, x_1735);
lean_dec(x_1727);
lean_inc(x_1709);
x_1737 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1737, 0, x_1413);
lean_ctor_set(x_1737, 1, x_1709);
lean_ctor_set(x_1737, 2, x_1733);
x_1738 = lean_array_uset(x_1728, x_1732, x_1737);
x_1739 = lean_unsigned_to_nat(4u);
x_1740 = lean_nat_mul(x_1736, x_1739);
x_1741 = lean_unsigned_to_nat(3u);
x_1742 = lean_nat_div(x_1740, x_1741);
lean_dec(x_1740);
x_1743 = lean_array_get_size(x_1738);
x_1744 = lean_nat_dec_le(x_1742, x_1743);
lean_dec(x_1743);
lean_dec(x_1742);
if (x_1744 == 0)
{
lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; 
x_1745 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1738);
lean_ctor_set(x_1713, 1, x_1745);
lean_ctor_set(x_1713, 0, x_1736);
x_1746 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1746, 0, x_1715);
lean_ctor_set(x_1746, 1, x_1713);
lean_ctor_set(x_1746, 2, x_1716);
lean_ctor_set(x_1746, 3, x_1717);
lean_ctor_set(x_1746, 4, x_1718);
lean_ctor_set(x_1746, 5, x_1719);
lean_ctor_set(x_1746, 6, x_1720);
lean_ctor_set(x_1746, 7, x_1721);
lean_ctor_set(x_1746, 8, x_1722);
lean_ctor_set(x_1746, 9, x_1723);
lean_ctor_set(x_1746, 10, x_1724);
lean_ctor_set(x_1746, 11, x_1725);
x_1747 = lean_st_ref_set(x_3, x_1746, x_1714);
x_1748 = lean_ctor_get(x_1747, 1);
lean_inc(x_1748);
lean_dec(x_1747);
x_1416 = x_1709;
x_1417 = x_1748;
goto block_1686;
}
else
{
lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
lean_ctor_set(x_1713, 1, x_1738);
lean_ctor_set(x_1713, 0, x_1736);
x_1749 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1749, 0, x_1715);
lean_ctor_set(x_1749, 1, x_1713);
lean_ctor_set(x_1749, 2, x_1716);
lean_ctor_set(x_1749, 3, x_1717);
lean_ctor_set(x_1749, 4, x_1718);
lean_ctor_set(x_1749, 5, x_1719);
lean_ctor_set(x_1749, 6, x_1720);
lean_ctor_set(x_1749, 7, x_1721);
lean_ctor_set(x_1749, 8, x_1722);
lean_ctor_set(x_1749, 9, x_1723);
lean_ctor_set(x_1749, 10, x_1724);
lean_ctor_set(x_1749, 11, x_1725);
x_1750 = lean_st_ref_set(x_3, x_1749, x_1714);
x_1751 = lean_ctor_get(x_1750, 1);
lean_inc(x_1751);
lean_dec(x_1750);
x_1416 = x_1709;
x_1417 = x_1751;
goto block_1686;
}
}
else
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; 
x_1752 = lean_box(0);
x_1753 = lean_array_uset(x_1728, x_1732, x_1752);
lean_inc(x_1709);
x_1754 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1413, x_1709, x_1733);
x_1755 = lean_array_uset(x_1753, x_1732, x_1754);
lean_ctor_set(x_1713, 1, x_1755);
x_1756 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1756, 0, x_1715);
lean_ctor_set(x_1756, 1, x_1713);
lean_ctor_set(x_1756, 2, x_1716);
lean_ctor_set(x_1756, 3, x_1717);
lean_ctor_set(x_1756, 4, x_1718);
lean_ctor_set(x_1756, 5, x_1719);
lean_ctor_set(x_1756, 6, x_1720);
lean_ctor_set(x_1756, 7, x_1721);
lean_ctor_set(x_1756, 8, x_1722);
lean_ctor_set(x_1756, 9, x_1723);
lean_ctor_set(x_1756, 10, x_1724);
lean_ctor_set(x_1756, 11, x_1725);
x_1757 = lean_st_ref_set(x_3, x_1756, x_1714);
x_1758 = lean_ctor_get(x_1757, 1);
lean_inc(x_1758);
lean_dec(x_1757);
x_1416 = x_1709;
x_1417 = x_1758;
goto block_1686;
}
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; size_t x_1762; size_t x_1763; size_t x_1764; lean_object* x_1765; uint8_t x_1766; 
x_1759 = lean_ctor_get(x_1713, 0);
x_1760 = lean_ctor_get(x_1713, 1);
lean_inc(x_1760);
lean_inc(x_1759);
lean_dec(x_1713);
x_1761 = lean_array_get_size(x_1760);
x_1762 = lean_usize_of_nat(x_1761);
lean_dec(x_1761);
x_1763 = lean_usize_sub(x_1762, x_1703);
x_1764 = lean_usize_land(x_1701, x_1763);
x_1765 = lean_array_uget(x_1760, x_1764);
x_1766 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1413, x_1765);
if (x_1766 == 0)
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; uint8_t x_1776; 
x_1767 = lean_unsigned_to_nat(1u);
x_1768 = lean_nat_add(x_1759, x_1767);
lean_dec(x_1759);
lean_inc(x_1709);
x_1769 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1769, 0, x_1413);
lean_ctor_set(x_1769, 1, x_1709);
lean_ctor_set(x_1769, 2, x_1765);
x_1770 = lean_array_uset(x_1760, x_1764, x_1769);
x_1771 = lean_unsigned_to_nat(4u);
x_1772 = lean_nat_mul(x_1768, x_1771);
x_1773 = lean_unsigned_to_nat(3u);
x_1774 = lean_nat_div(x_1772, x_1773);
lean_dec(x_1772);
x_1775 = lean_array_get_size(x_1770);
x_1776 = lean_nat_dec_le(x_1774, x_1775);
lean_dec(x_1775);
lean_dec(x_1774);
if (x_1776 == 0)
{
lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
x_1777 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1770);
x_1778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1778, 0, x_1768);
lean_ctor_set(x_1778, 1, x_1777);
x_1779 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1779, 0, x_1715);
lean_ctor_set(x_1779, 1, x_1778);
lean_ctor_set(x_1779, 2, x_1716);
lean_ctor_set(x_1779, 3, x_1717);
lean_ctor_set(x_1779, 4, x_1718);
lean_ctor_set(x_1779, 5, x_1719);
lean_ctor_set(x_1779, 6, x_1720);
lean_ctor_set(x_1779, 7, x_1721);
lean_ctor_set(x_1779, 8, x_1722);
lean_ctor_set(x_1779, 9, x_1723);
lean_ctor_set(x_1779, 10, x_1724);
lean_ctor_set(x_1779, 11, x_1725);
x_1780 = lean_st_ref_set(x_3, x_1779, x_1714);
x_1781 = lean_ctor_get(x_1780, 1);
lean_inc(x_1781);
lean_dec(x_1780);
x_1416 = x_1709;
x_1417 = x_1781;
goto block_1686;
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; 
x_1782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1782, 0, x_1768);
lean_ctor_set(x_1782, 1, x_1770);
x_1783 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1783, 0, x_1715);
lean_ctor_set(x_1783, 1, x_1782);
lean_ctor_set(x_1783, 2, x_1716);
lean_ctor_set(x_1783, 3, x_1717);
lean_ctor_set(x_1783, 4, x_1718);
lean_ctor_set(x_1783, 5, x_1719);
lean_ctor_set(x_1783, 6, x_1720);
lean_ctor_set(x_1783, 7, x_1721);
lean_ctor_set(x_1783, 8, x_1722);
lean_ctor_set(x_1783, 9, x_1723);
lean_ctor_set(x_1783, 10, x_1724);
lean_ctor_set(x_1783, 11, x_1725);
x_1784 = lean_st_ref_set(x_3, x_1783, x_1714);
x_1785 = lean_ctor_get(x_1784, 1);
lean_inc(x_1785);
lean_dec(x_1784);
x_1416 = x_1709;
x_1417 = x_1785;
goto block_1686;
}
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
x_1786 = lean_box(0);
x_1787 = lean_array_uset(x_1760, x_1764, x_1786);
lean_inc(x_1709);
x_1788 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1413, x_1709, x_1765);
x_1789 = lean_array_uset(x_1787, x_1764, x_1788);
x_1790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1790, 0, x_1759);
lean_ctor_set(x_1790, 1, x_1789);
x_1791 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1791, 0, x_1715);
lean_ctor_set(x_1791, 1, x_1790);
lean_ctor_set(x_1791, 2, x_1716);
lean_ctor_set(x_1791, 3, x_1717);
lean_ctor_set(x_1791, 4, x_1718);
lean_ctor_set(x_1791, 5, x_1719);
lean_ctor_set(x_1791, 6, x_1720);
lean_ctor_set(x_1791, 7, x_1721);
lean_ctor_set(x_1791, 8, x_1722);
lean_ctor_set(x_1791, 9, x_1723);
lean_ctor_set(x_1791, 10, x_1724);
lean_ctor_set(x_1791, 11, x_1725);
x_1792 = lean_st_ref_set(x_3, x_1791, x_1714);
x_1793 = lean_ctor_get(x_1792, 1);
lean_inc(x_1793);
lean_dec(x_1792);
x_1416 = x_1709;
x_1417 = x_1793;
goto block_1686;
}
}
}
else
{
uint8_t x_1794; 
lean_dec(x_1415);
lean_dec(x_1414);
lean_dec(x_1413);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1794 = !lean_is_exclusive(x_1708);
if (x_1794 == 0)
{
return x_1708;
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
x_1795 = lean_ctor_get(x_1708, 0);
x_1796 = lean_ctor_get(x_1708, 1);
lean_inc(x_1796);
lean_inc(x_1795);
lean_dec(x_1708);
x_1797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1797, 0, x_1795);
lean_ctor_set(x_1797, 1, x_1796);
return x_1797;
}
}
}
else
{
lean_object* x_1798; 
lean_dec(x_1413);
x_1798 = lean_ctor_get(x_1707, 0);
lean_inc(x_1798);
lean_dec(x_1707);
x_1416 = x_1798;
x_1417 = x_1691;
goto block_1686;
}
}
}
case 10:
{
lean_object* x_1806; lean_object* x_1807; uint8_t x_1920; 
x_1806 = lean_ctor_get(x_1, 1);
lean_inc(x_1806);
x_1920 = l_Lean_Expr_hasLevelParam(x_1806);
if (x_1920 == 0)
{
uint8_t x_1921; 
x_1921 = l_Lean_Expr_hasFVar(x_1806);
if (x_1921 == 0)
{
uint8_t x_1922; 
x_1922 = l_Lean_Expr_hasMVar(x_1806);
if (x_1922 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_1806;
x_10 = x_8;
goto block_22;
}
else
{
lean_object* x_1923; 
x_1923 = lean_box(0);
x_1807 = x_1923;
goto block_1919;
}
}
else
{
lean_object* x_1924; 
x_1924 = lean_box(0);
x_1807 = x_1924;
goto block_1919;
}
}
else
{
lean_object* x_1925; 
x_1925 = lean_box(0);
x_1807 = x_1925;
goto block_1919;
}
block_1919:
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; uint64_t x_1814; uint64_t x_1815; uint64_t x_1816; uint64_t x_1817; uint64_t x_1818; uint64_t x_1819; uint64_t x_1820; size_t x_1821; size_t x_1822; size_t x_1823; size_t x_1824; size_t x_1825; lean_object* x_1826; lean_object* x_1827; 
lean_dec(x_1807);
x_1808 = lean_st_ref_get(x_3, x_8);
x_1809 = lean_ctor_get(x_1808, 0);
lean_inc(x_1809);
x_1810 = lean_ctor_get(x_1809, 1);
lean_inc(x_1810);
lean_dec(x_1809);
x_1811 = lean_ctor_get(x_1808, 1);
lean_inc(x_1811);
lean_dec(x_1808);
x_1812 = lean_ctor_get(x_1810, 1);
lean_inc(x_1812);
lean_dec(x_1810);
x_1813 = lean_array_get_size(x_1812);
x_1814 = l_Lean_Expr_hash(x_1806);
x_1815 = 32;
x_1816 = lean_uint64_shift_right(x_1814, x_1815);
x_1817 = lean_uint64_xor(x_1814, x_1816);
x_1818 = 16;
x_1819 = lean_uint64_shift_right(x_1817, x_1818);
x_1820 = lean_uint64_xor(x_1817, x_1819);
x_1821 = lean_uint64_to_usize(x_1820);
x_1822 = lean_usize_of_nat(x_1813);
lean_dec(x_1813);
x_1823 = 1;
x_1824 = lean_usize_sub(x_1822, x_1823);
x_1825 = lean_usize_land(x_1821, x_1824);
x_1826 = lean_array_uget(x_1812, x_1825);
lean_dec(x_1812);
x_1827 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1806, x_1826);
lean_dec(x_1826);
if (lean_obj_tag(x_1827) == 0)
{
lean_object* x_1828; 
lean_inc(x_1806);
x_1828 = l_Lean_Meta_Closure_collectExprAux(x_1806, x_2, x_3, x_4, x_5, x_6, x_7, x_1811);
if (lean_obj_tag(x_1828) == 0)
{
lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; uint8_t x_1846; 
x_1829 = lean_ctor_get(x_1828, 0);
lean_inc(x_1829);
x_1830 = lean_ctor_get(x_1828, 1);
lean_inc(x_1830);
lean_dec(x_1828);
x_1831 = lean_st_ref_take(x_3, x_1830);
x_1832 = lean_ctor_get(x_1831, 0);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1832, 1);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1831, 1);
lean_inc(x_1834);
lean_dec(x_1831);
x_1835 = lean_ctor_get(x_1832, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1832, 2);
lean_inc(x_1836);
x_1837 = lean_ctor_get(x_1832, 3);
lean_inc(x_1837);
x_1838 = lean_ctor_get(x_1832, 4);
lean_inc(x_1838);
x_1839 = lean_ctor_get(x_1832, 5);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1832, 6);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1832, 7);
lean_inc(x_1841);
x_1842 = lean_ctor_get(x_1832, 8);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1832, 9);
lean_inc(x_1843);
x_1844 = lean_ctor_get(x_1832, 10);
lean_inc(x_1844);
x_1845 = lean_ctor_get(x_1832, 11);
lean_inc(x_1845);
lean_dec(x_1832);
x_1846 = !lean_is_exclusive(x_1833);
if (x_1846 == 0)
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; size_t x_1850; size_t x_1851; size_t x_1852; lean_object* x_1853; uint8_t x_1854; 
x_1847 = lean_ctor_get(x_1833, 0);
x_1848 = lean_ctor_get(x_1833, 1);
x_1849 = lean_array_get_size(x_1848);
x_1850 = lean_usize_of_nat(x_1849);
lean_dec(x_1849);
x_1851 = lean_usize_sub(x_1850, x_1823);
x_1852 = lean_usize_land(x_1821, x_1851);
x_1853 = lean_array_uget(x_1848, x_1852);
x_1854 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1806, x_1853);
if (x_1854 == 0)
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; uint8_t x_1864; 
x_1855 = lean_unsigned_to_nat(1u);
x_1856 = lean_nat_add(x_1847, x_1855);
lean_dec(x_1847);
lean_inc(x_1829);
x_1857 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1857, 0, x_1806);
lean_ctor_set(x_1857, 1, x_1829);
lean_ctor_set(x_1857, 2, x_1853);
x_1858 = lean_array_uset(x_1848, x_1852, x_1857);
x_1859 = lean_unsigned_to_nat(4u);
x_1860 = lean_nat_mul(x_1856, x_1859);
x_1861 = lean_unsigned_to_nat(3u);
x_1862 = lean_nat_div(x_1860, x_1861);
lean_dec(x_1860);
x_1863 = lean_array_get_size(x_1858);
x_1864 = lean_nat_dec_le(x_1862, x_1863);
lean_dec(x_1863);
lean_dec(x_1862);
if (x_1864 == 0)
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; 
x_1865 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1858);
lean_ctor_set(x_1833, 1, x_1865);
lean_ctor_set(x_1833, 0, x_1856);
x_1866 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1866, 0, x_1835);
lean_ctor_set(x_1866, 1, x_1833);
lean_ctor_set(x_1866, 2, x_1836);
lean_ctor_set(x_1866, 3, x_1837);
lean_ctor_set(x_1866, 4, x_1838);
lean_ctor_set(x_1866, 5, x_1839);
lean_ctor_set(x_1866, 6, x_1840);
lean_ctor_set(x_1866, 7, x_1841);
lean_ctor_set(x_1866, 8, x_1842);
lean_ctor_set(x_1866, 9, x_1843);
lean_ctor_set(x_1866, 10, x_1844);
lean_ctor_set(x_1866, 11, x_1845);
x_1867 = lean_st_ref_set(x_3, x_1866, x_1834);
x_1868 = lean_ctor_get(x_1867, 1);
lean_inc(x_1868);
lean_dec(x_1867);
x_9 = x_1829;
x_10 = x_1868;
goto block_22;
}
else
{
lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; 
lean_ctor_set(x_1833, 1, x_1858);
lean_ctor_set(x_1833, 0, x_1856);
x_1869 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1869, 0, x_1835);
lean_ctor_set(x_1869, 1, x_1833);
lean_ctor_set(x_1869, 2, x_1836);
lean_ctor_set(x_1869, 3, x_1837);
lean_ctor_set(x_1869, 4, x_1838);
lean_ctor_set(x_1869, 5, x_1839);
lean_ctor_set(x_1869, 6, x_1840);
lean_ctor_set(x_1869, 7, x_1841);
lean_ctor_set(x_1869, 8, x_1842);
lean_ctor_set(x_1869, 9, x_1843);
lean_ctor_set(x_1869, 10, x_1844);
lean_ctor_set(x_1869, 11, x_1845);
x_1870 = lean_st_ref_set(x_3, x_1869, x_1834);
x_1871 = lean_ctor_get(x_1870, 1);
lean_inc(x_1871);
lean_dec(x_1870);
x_9 = x_1829;
x_10 = x_1871;
goto block_22;
}
}
else
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
x_1872 = lean_box(0);
x_1873 = lean_array_uset(x_1848, x_1852, x_1872);
lean_inc(x_1829);
x_1874 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1806, x_1829, x_1853);
x_1875 = lean_array_uset(x_1873, x_1852, x_1874);
lean_ctor_set(x_1833, 1, x_1875);
x_1876 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1876, 0, x_1835);
lean_ctor_set(x_1876, 1, x_1833);
lean_ctor_set(x_1876, 2, x_1836);
lean_ctor_set(x_1876, 3, x_1837);
lean_ctor_set(x_1876, 4, x_1838);
lean_ctor_set(x_1876, 5, x_1839);
lean_ctor_set(x_1876, 6, x_1840);
lean_ctor_set(x_1876, 7, x_1841);
lean_ctor_set(x_1876, 8, x_1842);
lean_ctor_set(x_1876, 9, x_1843);
lean_ctor_set(x_1876, 10, x_1844);
lean_ctor_set(x_1876, 11, x_1845);
x_1877 = lean_st_ref_set(x_3, x_1876, x_1834);
x_1878 = lean_ctor_get(x_1877, 1);
lean_inc(x_1878);
lean_dec(x_1877);
x_9 = x_1829;
x_10 = x_1878;
goto block_22;
}
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; size_t x_1882; size_t x_1883; size_t x_1884; lean_object* x_1885; uint8_t x_1886; 
x_1879 = lean_ctor_get(x_1833, 0);
x_1880 = lean_ctor_get(x_1833, 1);
lean_inc(x_1880);
lean_inc(x_1879);
lean_dec(x_1833);
x_1881 = lean_array_get_size(x_1880);
x_1882 = lean_usize_of_nat(x_1881);
lean_dec(x_1881);
x_1883 = lean_usize_sub(x_1882, x_1823);
x_1884 = lean_usize_land(x_1821, x_1883);
x_1885 = lean_array_uget(x_1880, x_1884);
x_1886 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1806, x_1885);
if (x_1886 == 0)
{
lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; uint8_t x_1896; 
x_1887 = lean_unsigned_to_nat(1u);
x_1888 = lean_nat_add(x_1879, x_1887);
lean_dec(x_1879);
lean_inc(x_1829);
x_1889 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1889, 0, x_1806);
lean_ctor_set(x_1889, 1, x_1829);
lean_ctor_set(x_1889, 2, x_1885);
x_1890 = lean_array_uset(x_1880, x_1884, x_1889);
x_1891 = lean_unsigned_to_nat(4u);
x_1892 = lean_nat_mul(x_1888, x_1891);
x_1893 = lean_unsigned_to_nat(3u);
x_1894 = lean_nat_div(x_1892, x_1893);
lean_dec(x_1892);
x_1895 = lean_array_get_size(x_1890);
x_1896 = lean_nat_dec_le(x_1894, x_1895);
lean_dec(x_1895);
lean_dec(x_1894);
if (x_1896 == 0)
{
lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; 
x_1897 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1890);
x_1898 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1898, 0, x_1888);
lean_ctor_set(x_1898, 1, x_1897);
x_1899 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1899, 0, x_1835);
lean_ctor_set(x_1899, 1, x_1898);
lean_ctor_set(x_1899, 2, x_1836);
lean_ctor_set(x_1899, 3, x_1837);
lean_ctor_set(x_1899, 4, x_1838);
lean_ctor_set(x_1899, 5, x_1839);
lean_ctor_set(x_1899, 6, x_1840);
lean_ctor_set(x_1899, 7, x_1841);
lean_ctor_set(x_1899, 8, x_1842);
lean_ctor_set(x_1899, 9, x_1843);
lean_ctor_set(x_1899, 10, x_1844);
lean_ctor_set(x_1899, 11, x_1845);
x_1900 = lean_st_ref_set(x_3, x_1899, x_1834);
x_1901 = lean_ctor_get(x_1900, 1);
lean_inc(x_1901);
lean_dec(x_1900);
x_9 = x_1829;
x_10 = x_1901;
goto block_22;
}
else
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
x_1902 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1902, 0, x_1888);
lean_ctor_set(x_1902, 1, x_1890);
x_1903 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1903, 0, x_1835);
lean_ctor_set(x_1903, 1, x_1902);
lean_ctor_set(x_1903, 2, x_1836);
lean_ctor_set(x_1903, 3, x_1837);
lean_ctor_set(x_1903, 4, x_1838);
lean_ctor_set(x_1903, 5, x_1839);
lean_ctor_set(x_1903, 6, x_1840);
lean_ctor_set(x_1903, 7, x_1841);
lean_ctor_set(x_1903, 8, x_1842);
lean_ctor_set(x_1903, 9, x_1843);
lean_ctor_set(x_1903, 10, x_1844);
lean_ctor_set(x_1903, 11, x_1845);
x_1904 = lean_st_ref_set(x_3, x_1903, x_1834);
x_1905 = lean_ctor_get(x_1904, 1);
lean_inc(x_1905);
lean_dec(x_1904);
x_9 = x_1829;
x_10 = x_1905;
goto block_22;
}
}
else
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; 
x_1906 = lean_box(0);
x_1907 = lean_array_uset(x_1880, x_1884, x_1906);
lean_inc(x_1829);
x_1908 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1806, x_1829, x_1885);
x_1909 = lean_array_uset(x_1907, x_1884, x_1908);
x_1910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1910, 0, x_1879);
lean_ctor_set(x_1910, 1, x_1909);
x_1911 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1911, 0, x_1835);
lean_ctor_set(x_1911, 1, x_1910);
lean_ctor_set(x_1911, 2, x_1836);
lean_ctor_set(x_1911, 3, x_1837);
lean_ctor_set(x_1911, 4, x_1838);
lean_ctor_set(x_1911, 5, x_1839);
lean_ctor_set(x_1911, 6, x_1840);
lean_ctor_set(x_1911, 7, x_1841);
lean_ctor_set(x_1911, 8, x_1842);
lean_ctor_set(x_1911, 9, x_1843);
lean_ctor_set(x_1911, 10, x_1844);
lean_ctor_set(x_1911, 11, x_1845);
x_1912 = lean_st_ref_set(x_3, x_1911, x_1834);
x_1913 = lean_ctor_get(x_1912, 1);
lean_inc(x_1913);
lean_dec(x_1912);
x_9 = x_1829;
x_10 = x_1913;
goto block_22;
}
}
}
else
{
uint8_t x_1914; 
lean_dec(x_1806);
lean_dec(x_1);
x_1914 = !lean_is_exclusive(x_1828);
if (x_1914 == 0)
{
return x_1828;
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; 
x_1915 = lean_ctor_get(x_1828, 0);
x_1916 = lean_ctor_get(x_1828, 1);
lean_inc(x_1916);
lean_inc(x_1915);
lean_dec(x_1828);
x_1917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1917, 0, x_1915);
lean_ctor_set(x_1917, 1, x_1916);
return x_1917;
}
}
}
else
{
lean_object* x_1918; 
lean_dec(x_1806);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1918 = lean_ctor_get(x_1827, 0);
lean_inc(x_1918);
lean_dec(x_1827);
x_9 = x_1918;
x_10 = x_1811;
goto block_22;
}
}
}
case 11:
{
lean_object* x_1926; lean_object* x_1927; uint8_t x_2040; 
x_1926 = lean_ctor_get(x_1, 2);
lean_inc(x_1926);
x_2040 = l_Lean_Expr_hasLevelParam(x_1926);
if (x_2040 == 0)
{
uint8_t x_2041; 
x_2041 = l_Lean_Expr_hasFVar(x_1926);
if (x_2041 == 0)
{
uint8_t x_2042; 
x_2042 = l_Lean_Expr_hasMVar(x_1926);
if (x_2042 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = x_1926;
x_24 = x_8;
goto block_37;
}
else
{
lean_object* x_2043; 
x_2043 = lean_box(0);
x_1927 = x_2043;
goto block_2039;
}
}
else
{
lean_object* x_2044; 
x_2044 = lean_box(0);
x_1927 = x_2044;
goto block_2039;
}
}
else
{
lean_object* x_2045; 
x_2045 = lean_box(0);
x_1927 = x_2045;
goto block_2039;
}
block_2039:
{
lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; uint64_t x_1934; uint64_t x_1935; uint64_t x_1936; uint64_t x_1937; uint64_t x_1938; uint64_t x_1939; uint64_t x_1940; size_t x_1941; size_t x_1942; size_t x_1943; size_t x_1944; size_t x_1945; lean_object* x_1946; lean_object* x_1947; 
lean_dec(x_1927);
x_1928 = lean_st_ref_get(x_3, x_8);
x_1929 = lean_ctor_get(x_1928, 0);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1929, 1);
lean_inc(x_1930);
lean_dec(x_1929);
x_1931 = lean_ctor_get(x_1928, 1);
lean_inc(x_1931);
lean_dec(x_1928);
x_1932 = lean_ctor_get(x_1930, 1);
lean_inc(x_1932);
lean_dec(x_1930);
x_1933 = lean_array_get_size(x_1932);
x_1934 = l_Lean_Expr_hash(x_1926);
x_1935 = 32;
x_1936 = lean_uint64_shift_right(x_1934, x_1935);
x_1937 = lean_uint64_xor(x_1934, x_1936);
x_1938 = 16;
x_1939 = lean_uint64_shift_right(x_1937, x_1938);
x_1940 = lean_uint64_xor(x_1937, x_1939);
x_1941 = lean_uint64_to_usize(x_1940);
x_1942 = lean_usize_of_nat(x_1933);
lean_dec(x_1933);
x_1943 = 1;
x_1944 = lean_usize_sub(x_1942, x_1943);
x_1945 = lean_usize_land(x_1941, x_1944);
x_1946 = lean_array_uget(x_1932, x_1945);
lean_dec(x_1932);
x_1947 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_1926, x_1946);
lean_dec(x_1946);
if (lean_obj_tag(x_1947) == 0)
{
lean_object* x_1948; 
lean_inc(x_1926);
x_1948 = l_Lean_Meta_Closure_collectExprAux(x_1926, x_2, x_3, x_4, x_5, x_6, x_7, x_1931);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; uint8_t x_1966; 
x_1949 = lean_ctor_get(x_1948, 0);
lean_inc(x_1949);
x_1950 = lean_ctor_get(x_1948, 1);
lean_inc(x_1950);
lean_dec(x_1948);
x_1951 = lean_st_ref_take(x_3, x_1950);
x_1952 = lean_ctor_get(x_1951, 0);
lean_inc(x_1952);
x_1953 = lean_ctor_get(x_1952, 1);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1951, 1);
lean_inc(x_1954);
lean_dec(x_1951);
x_1955 = lean_ctor_get(x_1952, 0);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1952, 2);
lean_inc(x_1956);
x_1957 = lean_ctor_get(x_1952, 3);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1952, 4);
lean_inc(x_1958);
x_1959 = lean_ctor_get(x_1952, 5);
lean_inc(x_1959);
x_1960 = lean_ctor_get(x_1952, 6);
lean_inc(x_1960);
x_1961 = lean_ctor_get(x_1952, 7);
lean_inc(x_1961);
x_1962 = lean_ctor_get(x_1952, 8);
lean_inc(x_1962);
x_1963 = lean_ctor_get(x_1952, 9);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1952, 10);
lean_inc(x_1964);
x_1965 = lean_ctor_get(x_1952, 11);
lean_inc(x_1965);
lean_dec(x_1952);
x_1966 = !lean_is_exclusive(x_1953);
if (x_1966 == 0)
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; size_t x_1970; size_t x_1971; size_t x_1972; lean_object* x_1973; uint8_t x_1974; 
x_1967 = lean_ctor_get(x_1953, 0);
x_1968 = lean_ctor_get(x_1953, 1);
x_1969 = lean_array_get_size(x_1968);
x_1970 = lean_usize_of_nat(x_1969);
lean_dec(x_1969);
x_1971 = lean_usize_sub(x_1970, x_1943);
x_1972 = lean_usize_land(x_1941, x_1971);
x_1973 = lean_array_uget(x_1968, x_1972);
x_1974 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1926, x_1973);
if (x_1974 == 0)
{
lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; uint8_t x_1984; 
x_1975 = lean_unsigned_to_nat(1u);
x_1976 = lean_nat_add(x_1967, x_1975);
lean_dec(x_1967);
lean_inc(x_1949);
x_1977 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1977, 0, x_1926);
lean_ctor_set(x_1977, 1, x_1949);
lean_ctor_set(x_1977, 2, x_1973);
x_1978 = lean_array_uset(x_1968, x_1972, x_1977);
x_1979 = lean_unsigned_to_nat(4u);
x_1980 = lean_nat_mul(x_1976, x_1979);
x_1981 = lean_unsigned_to_nat(3u);
x_1982 = lean_nat_div(x_1980, x_1981);
lean_dec(x_1980);
x_1983 = lean_array_get_size(x_1978);
x_1984 = lean_nat_dec_le(x_1982, x_1983);
lean_dec(x_1983);
lean_dec(x_1982);
if (x_1984 == 0)
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
x_1985 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_1978);
lean_ctor_set(x_1953, 1, x_1985);
lean_ctor_set(x_1953, 0, x_1976);
x_1986 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1986, 0, x_1955);
lean_ctor_set(x_1986, 1, x_1953);
lean_ctor_set(x_1986, 2, x_1956);
lean_ctor_set(x_1986, 3, x_1957);
lean_ctor_set(x_1986, 4, x_1958);
lean_ctor_set(x_1986, 5, x_1959);
lean_ctor_set(x_1986, 6, x_1960);
lean_ctor_set(x_1986, 7, x_1961);
lean_ctor_set(x_1986, 8, x_1962);
lean_ctor_set(x_1986, 9, x_1963);
lean_ctor_set(x_1986, 10, x_1964);
lean_ctor_set(x_1986, 11, x_1965);
x_1987 = lean_st_ref_set(x_3, x_1986, x_1954);
x_1988 = lean_ctor_get(x_1987, 1);
lean_inc(x_1988);
lean_dec(x_1987);
x_23 = x_1949;
x_24 = x_1988;
goto block_37;
}
else
{
lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; 
lean_ctor_set(x_1953, 1, x_1978);
lean_ctor_set(x_1953, 0, x_1976);
x_1989 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1989, 0, x_1955);
lean_ctor_set(x_1989, 1, x_1953);
lean_ctor_set(x_1989, 2, x_1956);
lean_ctor_set(x_1989, 3, x_1957);
lean_ctor_set(x_1989, 4, x_1958);
lean_ctor_set(x_1989, 5, x_1959);
lean_ctor_set(x_1989, 6, x_1960);
lean_ctor_set(x_1989, 7, x_1961);
lean_ctor_set(x_1989, 8, x_1962);
lean_ctor_set(x_1989, 9, x_1963);
lean_ctor_set(x_1989, 10, x_1964);
lean_ctor_set(x_1989, 11, x_1965);
x_1990 = lean_st_ref_set(x_3, x_1989, x_1954);
x_1991 = lean_ctor_get(x_1990, 1);
lean_inc(x_1991);
lean_dec(x_1990);
x_23 = x_1949;
x_24 = x_1991;
goto block_37;
}
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
x_1992 = lean_box(0);
x_1993 = lean_array_uset(x_1968, x_1972, x_1992);
lean_inc(x_1949);
x_1994 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1926, x_1949, x_1973);
x_1995 = lean_array_uset(x_1993, x_1972, x_1994);
lean_ctor_set(x_1953, 1, x_1995);
x_1996 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1996, 0, x_1955);
lean_ctor_set(x_1996, 1, x_1953);
lean_ctor_set(x_1996, 2, x_1956);
lean_ctor_set(x_1996, 3, x_1957);
lean_ctor_set(x_1996, 4, x_1958);
lean_ctor_set(x_1996, 5, x_1959);
lean_ctor_set(x_1996, 6, x_1960);
lean_ctor_set(x_1996, 7, x_1961);
lean_ctor_set(x_1996, 8, x_1962);
lean_ctor_set(x_1996, 9, x_1963);
lean_ctor_set(x_1996, 10, x_1964);
lean_ctor_set(x_1996, 11, x_1965);
x_1997 = lean_st_ref_set(x_3, x_1996, x_1954);
x_1998 = lean_ctor_get(x_1997, 1);
lean_inc(x_1998);
lean_dec(x_1997);
x_23 = x_1949;
x_24 = x_1998;
goto block_37;
}
}
else
{
lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; size_t x_2002; size_t x_2003; size_t x_2004; lean_object* x_2005; uint8_t x_2006; 
x_1999 = lean_ctor_get(x_1953, 0);
x_2000 = lean_ctor_get(x_1953, 1);
lean_inc(x_2000);
lean_inc(x_1999);
lean_dec(x_1953);
x_2001 = lean_array_get_size(x_2000);
x_2002 = lean_usize_of_nat(x_2001);
lean_dec(x_2001);
x_2003 = lean_usize_sub(x_2002, x_1943);
x_2004 = lean_usize_land(x_1941, x_2003);
x_2005 = lean_array_uget(x_2000, x_2004);
x_2006 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_1926, x_2005);
if (x_2006 == 0)
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; uint8_t x_2016; 
x_2007 = lean_unsigned_to_nat(1u);
x_2008 = lean_nat_add(x_1999, x_2007);
lean_dec(x_1999);
lean_inc(x_1949);
x_2009 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2009, 0, x_1926);
lean_ctor_set(x_2009, 1, x_1949);
lean_ctor_set(x_2009, 2, x_2005);
x_2010 = lean_array_uset(x_2000, x_2004, x_2009);
x_2011 = lean_unsigned_to_nat(4u);
x_2012 = lean_nat_mul(x_2008, x_2011);
x_2013 = lean_unsigned_to_nat(3u);
x_2014 = lean_nat_div(x_2012, x_2013);
lean_dec(x_2012);
x_2015 = lean_array_get_size(x_2010);
x_2016 = lean_nat_dec_le(x_2014, x_2015);
lean_dec(x_2015);
lean_dec(x_2014);
if (x_2016 == 0)
{
lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; 
x_2017 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_2010);
x_2018 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2018, 0, x_2008);
lean_ctor_set(x_2018, 1, x_2017);
x_2019 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_2019, 0, x_1955);
lean_ctor_set(x_2019, 1, x_2018);
lean_ctor_set(x_2019, 2, x_1956);
lean_ctor_set(x_2019, 3, x_1957);
lean_ctor_set(x_2019, 4, x_1958);
lean_ctor_set(x_2019, 5, x_1959);
lean_ctor_set(x_2019, 6, x_1960);
lean_ctor_set(x_2019, 7, x_1961);
lean_ctor_set(x_2019, 8, x_1962);
lean_ctor_set(x_2019, 9, x_1963);
lean_ctor_set(x_2019, 10, x_1964);
lean_ctor_set(x_2019, 11, x_1965);
x_2020 = lean_st_ref_set(x_3, x_2019, x_1954);
x_2021 = lean_ctor_get(x_2020, 1);
lean_inc(x_2021);
lean_dec(x_2020);
x_23 = x_1949;
x_24 = x_2021;
goto block_37;
}
else
{
lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; 
x_2022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2022, 0, x_2008);
lean_ctor_set(x_2022, 1, x_2010);
x_2023 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_2023, 0, x_1955);
lean_ctor_set(x_2023, 1, x_2022);
lean_ctor_set(x_2023, 2, x_1956);
lean_ctor_set(x_2023, 3, x_1957);
lean_ctor_set(x_2023, 4, x_1958);
lean_ctor_set(x_2023, 5, x_1959);
lean_ctor_set(x_2023, 6, x_1960);
lean_ctor_set(x_2023, 7, x_1961);
lean_ctor_set(x_2023, 8, x_1962);
lean_ctor_set(x_2023, 9, x_1963);
lean_ctor_set(x_2023, 10, x_1964);
lean_ctor_set(x_2023, 11, x_1965);
x_2024 = lean_st_ref_set(x_3, x_2023, x_1954);
x_2025 = lean_ctor_get(x_2024, 1);
lean_inc(x_2025);
lean_dec(x_2024);
x_23 = x_1949;
x_24 = x_2025;
goto block_37;
}
}
else
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; 
x_2026 = lean_box(0);
x_2027 = lean_array_uset(x_2000, x_2004, x_2026);
lean_inc(x_1949);
x_2028 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_1926, x_1949, x_2005);
x_2029 = lean_array_uset(x_2027, x_2004, x_2028);
x_2030 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2030, 0, x_1999);
lean_ctor_set(x_2030, 1, x_2029);
x_2031 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_2031, 0, x_1955);
lean_ctor_set(x_2031, 1, x_2030);
lean_ctor_set(x_2031, 2, x_1956);
lean_ctor_set(x_2031, 3, x_1957);
lean_ctor_set(x_2031, 4, x_1958);
lean_ctor_set(x_2031, 5, x_1959);
lean_ctor_set(x_2031, 6, x_1960);
lean_ctor_set(x_2031, 7, x_1961);
lean_ctor_set(x_2031, 8, x_1962);
lean_ctor_set(x_2031, 9, x_1963);
lean_ctor_set(x_2031, 10, x_1964);
lean_ctor_set(x_2031, 11, x_1965);
x_2032 = lean_st_ref_set(x_3, x_2031, x_1954);
x_2033 = lean_ctor_get(x_2032, 1);
lean_inc(x_2033);
lean_dec(x_2032);
x_23 = x_1949;
x_24 = x_2033;
goto block_37;
}
}
}
else
{
uint8_t x_2034; 
lean_dec(x_1926);
lean_dec(x_1);
x_2034 = !lean_is_exclusive(x_1948);
if (x_2034 == 0)
{
return x_1948;
}
else
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; 
x_2035 = lean_ctor_get(x_1948, 0);
x_2036 = lean_ctor_get(x_1948, 1);
lean_inc(x_2036);
lean_inc(x_2035);
lean_dec(x_1948);
x_2037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2037, 0, x_2035);
lean_ctor_set(x_2037, 1, x_2036);
return x_2037;
}
}
}
else
{
lean_object* x_2038; 
lean_dec(x_1926);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2038 = lean_ctor_get(x_1947, 0);
lean_inc(x_2038);
lean_dec(x_1947);
x_23 = x_2038;
x_24 = x_1931;
goto block_37;
}
}
}
default: 
{
lean_object* x_2046; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2046, 0, x_1);
lean_ctor_set(x_2046, 1, x_8);
return x_2046;
}
}
block_22:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_14 = lean_ptr_addr(x_9);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Expr_mdata___override(x_11, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = l_Lean_Meta_Closure_collectExprAux___closed__4;
x_20 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
block_37:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_29 = lean_ptr_addr(x_23);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = l_Lean_Expr_proj___override(x_25, x_26, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_1);
x_34 = l_Lean_Meta_Closure_collectExprAux___closed__7;
x_35 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_Closure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_265; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_265 = l_Lean_Expr_hasLevelParam(x_11);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = l_Lean_Expr_hasFVar(x_11);
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = l_Lean_Expr_hasMVar(x_11);
if (x_267 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_268; 
lean_free_object(x_9);
x_268 = lean_box(0);
x_13 = x_268;
goto block_264;
}
}
else
{
lean_object* x_269; 
lean_free_object(x_9);
x_269 = lean_box(0);
x_13 = x_269;
goto block_264;
}
}
else
{
lean_object* x_270; 
lean_free_object(x_9);
x_270 = lean_box(0);
x_13 = x_270;
goto block_264;
}
block_264:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_3, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_array_get_size(x_20);
x_22 = l_Lean_Expr_hash(x_11);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_20, x_33);
lean_dec(x_20);
x_35 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_11, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_free_object(x_14);
lean_inc(x_11);
x_36 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_3, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
x_48 = lean_array_get_size(x_47);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = lean_usize_sub(x_49, x_31);
x_51 = lean_usize_land(x_29, x_50);
x_52 = lean_array_uget(x_47, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_11, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_46, x_54);
lean_dec(x_46);
lean_inc(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_47, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_57);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_55);
x_65 = lean_st_ref_set(x_3, x_40, x_42);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_37);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_37);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_ctor_set(x_41, 1, x_57);
lean_ctor_set(x_41, 0, x_55);
x_70 = lean_st_ref_set(x_3, x_40, x_42);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_37);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_37);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_47, x_51, x_75);
lean_inc(x_37);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_11, x_37, x_52);
x_78 = lean_array_uset(x_76, x_51, x_77);
lean_ctor_set(x_41, 1, x_78);
x_79 = lean_st_ref_set(x_3, x_40, x_42);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_37);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_37);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; uint8_t x_91; 
x_84 = lean_ctor_get(x_41, 0);
x_85 = lean_ctor_get(x_41, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_41);
x_86 = lean_array_get_size(x_85);
x_87 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_88 = lean_usize_sub(x_87, x_31);
x_89 = lean_usize_land(x_29, x_88);
x_90 = lean_array_uget(x_85, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_11, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_84, x_92);
lean_dec(x_84);
lean_inc(x_37);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_37);
lean_ctor_set(x_94, 2, x_90);
x_95 = lean_array_uset(x_85, x_89, x_94);
x_96 = lean_unsigned_to_nat(4u);
x_97 = lean_nat_mul(x_93, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_nat_div(x_97, x_98);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
x_101 = lean_nat_dec_le(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_95);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_40, 1, x_103);
x_104 = lean_st_ref_set(x_3, x_40, x_42);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_95);
lean_ctor_set(x_40, 1, x_108);
x_109 = lean_st_ref_set(x_3, x_40, x_42);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_37);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_box(0);
x_114 = lean_array_uset(x_85, x_89, x_113);
lean_inc(x_37);
x_115 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_11, x_37, x_90);
x_116 = lean_array_uset(x_114, x_89, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_84);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_40, 1, x_117);
x_118 = lean_st_ref_set(x_3, x_40, x_42);
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
lean_ctor_set(x_121, 0, x_37);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; size_t x_137; size_t x_138; size_t x_139; lean_object* x_140; uint8_t x_141; 
x_122 = lean_ctor_get(x_40, 0);
x_123 = lean_ctor_get(x_40, 2);
x_124 = lean_ctor_get(x_40, 3);
x_125 = lean_ctor_get(x_40, 4);
x_126 = lean_ctor_get(x_40, 5);
x_127 = lean_ctor_get(x_40, 6);
x_128 = lean_ctor_get(x_40, 7);
x_129 = lean_ctor_get(x_40, 8);
x_130 = lean_ctor_get(x_40, 9);
x_131 = lean_ctor_get(x_40, 10);
x_132 = lean_ctor_get(x_40, 11);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_40);
x_133 = lean_ctor_get(x_41, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_41, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_135 = x_41;
} else {
 lean_dec_ref(x_41);
 x_135 = lean_box(0);
}
x_136 = lean_array_get_size(x_134);
x_137 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_138 = lean_usize_sub(x_137, x_31);
x_139 = lean_usize_land(x_29, x_138);
x_140 = lean_array_uget(x_134, x_139);
x_141 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_11, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_133, x_142);
lean_dec(x_133);
lean_inc(x_37);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_11);
lean_ctor_set(x_144, 1, x_37);
lean_ctor_set(x_144, 2, x_140);
x_145 = lean_array_uset(x_134, x_139, x_144);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_mul(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_145);
if (lean_is_scalar(x_135)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_135;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_154, 0, x_122);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_123);
lean_ctor_set(x_154, 3, x_124);
lean_ctor_set(x_154, 4, x_125);
lean_ctor_set(x_154, 5, x_126);
lean_ctor_set(x_154, 6, x_127);
lean_ctor_set(x_154, 7, x_128);
lean_ctor_set(x_154, 8, x_129);
lean_ctor_set(x_154, 9, x_130);
lean_ctor_set(x_154, 10, x_131);
lean_ctor_set(x_154, 11, x_132);
x_155 = lean_st_ref_set(x_3, x_154, x_42);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_37);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
if (lean_is_scalar(x_135)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_135;
}
lean_ctor_set(x_159, 0, x_143);
lean_ctor_set(x_159, 1, x_145);
x_160 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_160, 0, x_122);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_123);
lean_ctor_set(x_160, 3, x_124);
lean_ctor_set(x_160, 4, x_125);
lean_ctor_set(x_160, 5, x_126);
lean_ctor_set(x_160, 6, x_127);
lean_ctor_set(x_160, 7, x_128);
lean_ctor_set(x_160, 8, x_129);
lean_ctor_set(x_160, 9, x_130);
lean_ctor_set(x_160, 10, x_131);
lean_ctor_set(x_160, 11, x_132);
x_161 = lean_st_ref_set(x_3, x_160, x_42);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_37);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_box(0);
x_166 = lean_array_uset(x_134, x_139, x_165);
lean_inc(x_37);
x_167 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_11, x_37, x_140);
x_168 = lean_array_uset(x_166, x_139, x_167);
if (lean_is_scalar(x_135)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_135;
}
lean_ctor_set(x_169, 0, x_133);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_170, 0, x_122);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_123);
lean_ctor_set(x_170, 3, x_124);
lean_ctor_set(x_170, 4, x_125);
lean_ctor_set(x_170, 5, x_126);
lean_ctor_set(x_170, 6, x_127);
lean_ctor_set(x_170, 7, x_128);
lean_ctor_set(x_170, 8, x_129);
lean_ctor_set(x_170, 9, x_130);
lean_ctor_set(x_170, 10, x_131);
lean_ctor_set(x_170, 11, x_132);
x_171 = lean_st_ref_set(x_3, x_170, x_42);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_37);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_11);
x_175 = !lean_is_exclusive(x_36);
if (x_175 == 0)
{
return x_36;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_36, 0);
x_177 = lean_ctor_get(x_36, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_36);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = lean_ctor_get(x_35, 0);
lean_inc(x_179);
lean_dec(x_35);
lean_ctor_set(x_14, 0, x_179);
return x_14;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; size_t x_190; size_t x_191; size_t x_192; size_t x_193; size_t x_194; lean_object* x_195; lean_object* x_196; 
x_180 = lean_ctor_get(x_14, 1);
lean_inc(x_180);
lean_dec(x_14);
x_181 = lean_ctor_get(x_16, 1);
lean_inc(x_181);
lean_dec(x_16);
x_182 = lean_array_get_size(x_181);
x_183 = l_Lean_Expr_hash(x_11);
x_184 = 32;
x_185 = lean_uint64_shift_right(x_183, x_184);
x_186 = lean_uint64_xor(x_183, x_185);
x_187 = 16;
x_188 = lean_uint64_shift_right(x_186, x_187);
x_189 = lean_uint64_xor(x_186, x_188);
x_190 = lean_uint64_to_usize(x_189);
x_191 = lean_usize_of_nat(x_182);
lean_dec(x_182);
x_192 = 1;
x_193 = lean_usize_sub(x_191, x_192);
x_194 = lean_usize_land(x_190, x_193);
x_195 = lean_array_uget(x_181, x_194);
lean_dec(x_181);
x_196 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_11, x_195);
lean_dec(x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
lean_inc(x_11);
x_197 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; size_t x_220; size_t x_221; size_t x_222; lean_object* x_223; uint8_t x_224; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_st_ref_take(x_3, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 5);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 6);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 8);
lean_inc(x_211);
x_212 = lean_ctor_get(x_201, 9);
lean_inc(x_212);
x_213 = lean_ctor_get(x_201, 10);
lean_inc(x_213);
x_214 = lean_ctor_get(x_201, 11);
lean_inc(x_214);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 lean_ctor_release(x_201, 6);
 lean_ctor_release(x_201, 7);
 lean_ctor_release(x_201, 8);
 lean_ctor_release(x_201, 9);
 lean_ctor_release(x_201, 10);
 lean_ctor_release(x_201, 11);
 x_215 = x_201;
} else {
 lean_dec_ref(x_201);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_202, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_202, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_218 = x_202;
} else {
 lean_dec_ref(x_202);
 x_218 = lean_box(0);
}
x_219 = lean_array_get_size(x_217);
x_220 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_221 = lean_usize_sub(x_220, x_192);
x_222 = lean_usize_land(x_190, x_221);
x_223 = lean_array_uget(x_217, x_222);
x_224 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_11, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_add(x_216, x_225);
lean_dec(x_216);
lean_inc(x_198);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_11);
lean_ctor_set(x_227, 1, x_198);
lean_ctor_set(x_227, 2, x_223);
x_228 = lean_array_uset(x_217, x_222, x_227);
x_229 = lean_unsigned_to_nat(4u);
x_230 = lean_nat_mul(x_226, x_229);
x_231 = lean_unsigned_to_nat(3u);
x_232 = lean_nat_div(x_230, x_231);
lean_dec(x_230);
x_233 = lean_array_get_size(x_228);
x_234 = lean_nat_dec_le(x_232, x_233);
lean_dec(x_233);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_228);
if (lean_is_scalar(x_218)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_218;
}
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_235);
if (lean_is_scalar(x_215)) {
 x_237 = lean_alloc_ctor(0, 12, 0);
} else {
 x_237 = x_215;
}
lean_ctor_set(x_237, 0, x_204);
lean_ctor_set(x_237, 1, x_236);
lean_ctor_set(x_237, 2, x_205);
lean_ctor_set(x_237, 3, x_206);
lean_ctor_set(x_237, 4, x_207);
lean_ctor_set(x_237, 5, x_208);
lean_ctor_set(x_237, 6, x_209);
lean_ctor_set(x_237, 7, x_210);
lean_ctor_set(x_237, 8, x_211);
lean_ctor_set(x_237, 9, x_212);
lean_ctor_set(x_237, 10, x_213);
lean_ctor_set(x_237, 11, x_214);
x_238 = lean_st_ref_set(x_3, x_237, x_203);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_198);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
if (lean_is_scalar(x_218)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_218;
}
lean_ctor_set(x_242, 0, x_226);
lean_ctor_set(x_242, 1, x_228);
if (lean_is_scalar(x_215)) {
 x_243 = lean_alloc_ctor(0, 12, 0);
} else {
 x_243 = x_215;
}
lean_ctor_set(x_243, 0, x_204);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_205);
lean_ctor_set(x_243, 3, x_206);
lean_ctor_set(x_243, 4, x_207);
lean_ctor_set(x_243, 5, x_208);
lean_ctor_set(x_243, 6, x_209);
lean_ctor_set(x_243, 7, x_210);
lean_ctor_set(x_243, 8, x_211);
lean_ctor_set(x_243, 9, x_212);
lean_ctor_set(x_243, 10, x_213);
lean_ctor_set(x_243, 11, x_214);
x_244 = lean_st_ref_set(x_3, x_243, x_203);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_198);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_248 = lean_box(0);
x_249 = lean_array_uset(x_217, x_222, x_248);
lean_inc(x_198);
x_250 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_11, x_198, x_223);
x_251 = lean_array_uset(x_249, x_222, x_250);
if (lean_is_scalar(x_218)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_218;
}
lean_ctor_set(x_252, 0, x_216);
lean_ctor_set(x_252, 1, x_251);
if (lean_is_scalar(x_215)) {
 x_253 = lean_alloc_ctor(0, 12, 0);
} else {
 x_253 = x_215;
}
lean_ctor_set(x_253, 0, x_204);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_205);
lean_ctor_set(x_253, 3, x_206);
lean_ctor_set(x_253, 4, x_207);
lean_ctor_set(x_253, 5, x_208);
lean_ctor_set(x_253, 6, x_209);
lean_ctor_set(x_253, 7, x_210);
lean_ctor_set(x_253, 8, x_211);
lean_ctor_set(x_253, 9, x_212);
lean_ctor_set(x_253, 10, x_213);
lean_ctor_set(x_253, 11, x_214);
x_254 = lean_st_ref_set(x_3, x_253, x_203);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_198);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_11);
x_258 = lean_ctor_get(x_197, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_197, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_260 = x_197;
} else {
 lean_dec_ref(x_197);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_262 = lean_ctor_get(x_196, 0);
lean_inc(x_262);
lean_dec(x_196);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_180);
return x_263;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_363; 
x_271 = lean_ctor_get(x_9, 0);
x_272 = lean_ctor_get(x_9, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_9);
x_363 = l_Lean_Expr_hasLevelParam(x_271);
if (x_363 == 0)
{
uint8_t x_364; 
x_364 = l_Lean_Expr_hasFVar(x_271);
if (x_364 == 0)
{
uint8_t x_365; 
x_365 = l_Lean_Expr_hasMVar(x_271);
if (x_365 == 0)
{
lean_object* x_366; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_271);
lean_ctor_set(x_366, 1, x_272);
return x_366;
}
else
{
lean_object* x_367; 
x_367 = lean_box(0);
x_273 = x_367;
goto block_362;
}
}
else
{
lean_object* x_368; 
x_368 = lean_box(0);
x_273 = x_368;
goto block_362;
}
}
else
{
lean_object* x_369; 
x_369 = lean_box(0);
x_273 = x_369;
goto block_362;
}
block_362:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint64_t x_281; uint64_t x_282; uint64_t x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; uint64_t x_287; size_t x_288; size_t x_289; size_t x_290; size_t x_291; size_t x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_273);
x_274 = lean_st_ref_get(x_3, x_272);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_278 = x_274;
} else {
 lean_dec_ref(x_274);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = lean_array_get_size(x_279);
x_281 = l_Lean_Expr_hash(x_271);
x_282 = 32;
x_283 = lean_uint64_shift_right(x_281, x_282);
x_284 = lean_uint64_xor(x_281, x_283);
x_285 = 16;
x_286 = lean_uint64_shift_right(x_284, x_285);
x_287 = lean_uint64_xor(x_284, x_286);
x_288 = lean_uint64_to_usize(x_287);
x_289 = lean_usize_of_nat(x_280);
lean_dec(x_280);
x_290 = 1;
x_291 = lean_usize_sub(x_289, x_290);
x_292 = lean_usize_land(x_288, x_291);
x_293 = lean_array_uget(x_279, x_292);
lean_dec(x_279);
x_294 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__1(x_271, x_293);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
lean_dec(x_278);
lean_inc(x_271);
x_295 = l_Lean_Meta_Closure_collectExprAux(x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_277);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; size_t x_318; size_t x_319; size_t x_320; lean_object* x_321; uint8_t x_322; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_st_ref_take(x_3, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_299, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_299, 3);
lean_inc(x_304);
x_305 = lean_ctor_get(x_299, 4);
lean_inc(x_305);
x_306 = lean_ctor_get(x_299, 5);
lean_inc(x_306);
x_307 = lean_ctor_get(x_299, 6);
lean_inc(x_307);
x_308 = lean_ctor_get(x_299, 7);
lean_inc(x_308);
x_309 = lean_ctor_get(x_299, 8);
lean_inc(x_309);
x_310 = lean_ctor_get(x_299, 9);
lean_inc(x_310);
x_311 = lean_ctor_get(x_299, 10);
lean_inc(x_311);
x_312 = lean_ctor_get(x_299, 11);
lean_inc(x_312);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 lean_ctor_release(x_299, 2);
 lean_ctor_release(x_299, 3);
 lean_ctor_release(x_299, 4);
 lean_ctor_release(x_299, 5);
 lean_ctor_release(x_299, 6);
 lean_ctor_release(x_299, 7);
 lean_ctor_release(x_299, 8);
 lean_ctor_release(x_299, 9);
 lean_ctor_release(x_299, 10);
 lean_ctor_release(x_299, 11);
 x_313 = x_299;
} else {
 lean_dec_ref(x_299);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_300, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_300, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_316 = x_300;
} else {
 lean_dec_ref(x_300);
 x_316 = lean_box(0);
}
x_317 = lean_array_get_size(x_315);
x_318 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_319 = lean_usize_sub(x_318, x_290);
x_320 = lean_usize_land(x_288, x_319);
x_321 = lean_array_uget(x_315, x_320);
x_322 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__2(x_271, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_nat_add(x_314, x_323);
lean_dec(x_314);
lean_inc(x_296);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_271);
lean_ctor_set(x_325, 1, x_296);
lean_ctor_set(x_325, 2, x_321);
x_326 = lean_array_uset(x_315, x_320, x_325);
x_327 = lean_unsigned_to_nat(4u);
x_328 = lean_nat_mul(x_324, x_327);
x_329 = lean_unsigned_to_nat(3u);
x_330 = lean_nat_div(x_328, x_329);
lean_dec(x_328);
x_331 = lean_array_get_size(x_326);
x_332 = lean_nat_dec_le(x_330, x_331);
lean_dec(x_331);
lean_dec(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_333 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__3(x_326);
if (lean_is_scalar(x_316)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_316;
}
lean_ctor_set(x_334, 0, x_324);
lean_ctor_set(x_334, 1, x_333);
if (lean_is_scalar(x_313)) {
 x_335 = lean_alloc_ctor(0, 12, 0);
} else {
 x_335 = x_313;
}
lean_ctor_set(x_335, 0, x_302);
lean_ctor_set(x_335, 1, x_334);
lean_ctor_set(x_335, 2, x_303);
lean_ctor_set(x_335, 3, x_304);
lean_ctor_set(x_335, 4, x_305);
lean_ctor_set(x_335, 5, x_306);
lean_ctor_set(x_335, 6, x_307);
lean_ctor_set(x_335, 7, x_308);
lean_ctor_set(x_335, 8, x_309);
lean_ctor_set(x_335, 9, x_310);
lean_ctor_set(x_335, 10, x_311);
lean_ctor_set(x_335, 11, x_312);
x_336 = lean_st_ref_set(x_3, x_335, x_301);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_296);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
if (lean_is_scalar(x_316)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_316;
}
lean_ctor_set(x_340, 0, x_324);
lean_ctor_set(x_340, 1, x_326);
if (lean_is_scalar(x_313)) {
 x_341 = lean_alloc_ctor(0, 12, 0);
} else {
 x_341 = x_313;
}
lean_ctor_set(x_341, 0, x_302);
lean_ctor_set(x_341, 1, x_340);
lean_ctor_set(x_341, 2, x_303);
lean_ctor_set(x_341, 3, x_304);
lean_ctor_set(x_341, 4, x_305);
lean_ctor_set(x_341, 5, x_306);
lean_ctor_set(x_341, 6, x_307);
lean_ctor_set(x_341, 7, x_308);
lean_ctor_set(x_341, 8, x_309);
lean_ctor_set(x_341, 9, x_310);
lean_ctor_set(x_341, 10, x_311);
lean_ctor_set(x_341, 11, x_312);
x_342 = lean_st_ref_set(x_3, x_341, x_301);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_296);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_346 = lean_box(0);
x_347 = lean_array_uset(x_315, x_320, x_346);
lean_inc(x_296);
x_348 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___spec__6(x_271, x_296, x_321);
x_349 = lean_array_uset(x_347, x_320, x_348);
if (lean_is_scalar(x_316)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_316;
}
lean_ctor_set(x_350, 0, x_314);
lean_ctor_set(x_350, 1, x_349);
if (lean_is_scalar(x_313)) {
 x_351 = lean_alloc_ctor(0, 12, 0);
} else {
 x_351 = x_313;
}
lean_ctor_set(x_351, 0, x_302);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_351, 2, x_303);
lean_ctor_set(x_351, 3, x_304);
lean_ctor_set(x_351, 4, x_305);
lean_ctor_set(x_351, 5, x_306);
lean_ctor_set(x_351, 6, x_307);
lean_ctor_set(x_351, 7, x_308);
lean_ctor_set(x_351, 8, x_309);
lean_ctor_set(x_351, 9, x_310);
lean_ctor_set(x_351, 10, x_311);
lean_ctor_set(x_351, 11, x_312);
x_352 = lean_st_ref_set(x_3, x_351, x_301);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_296);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_271);
x_356 = lean_ctor_get(x_295, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_295, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_358 = x_295;
} else {
 lean_dec_ref(x_295);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_271);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_360 = lean_ctor_get(x_294, 0);
lean_inc(x_360);
lean_dec(x_294);
if (lean_is_scalar(x_278)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_278;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_277);
return x_361;
}
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_370 = !lean_is_exclusive(x_9);
if (x_370 == 0)
{
return x_9;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_9, 0);
x_372 = lean_ctor_get(x_9, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_9);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExpr(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
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
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_LocalContext_get_x21(x_1, x_9);
x_11 = l_Lean_LocalDecl_index(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l_Lean_LocalContext_get_x21(x_1, x_12);
x_14 = l_Lean_LocalDecl_index(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_lt(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
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
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_st_ref_get(x_1, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 11);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_isEmpty___rarg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_8);
x_14 = lean_st_ref_take(x_1, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_15, 11);
x_19 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_20 = l_Array_back___rarg(x_19, x_18);
x_21 = lean_array_pop(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_22, x_21, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_15, 11, x_25);
x_27 = lean_st_ref_set(x_1, x_15, x_16);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
x_34 = lean_ctor_get(x_15, 2);
x_35 = lean_ctor_get(x_15, 3);
x_36 = lean_ctor_get(x_15, 4);
x_37 = lean_ctor_get(x_15, 5);
x_38 = lean_ctor_get(x_15, 6);
x_39 = lean_ctor_get(x_15, 7);
x_40 = lean_ctor_get(x_15, 8);
x_41 = lean_ctor_get(x_15, 9);
x_42 = lean_ctor_get(x_15, 10);
x_43 = lean_ctor_get(x_15, 11);
lean_inc(x_43);
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
lean_dec(x_15);
x_44 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_45 = l_Array_back___rarg(x_44, x_43);
x_46 = lean_array_pop(x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_47, x_46, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_33);
lean_ctor_set(x_52, 2, x_34);
lean_ctor_set(x_52, 3, x_35);
lean_ctor_set(x_52, 4, x_36);
lean_ctor_set(x_52, 5, x_37);
lean_ctor_set(x_52, 6, x_38);
lean_ctor_set(x_52, 7, x_39);
lean_ctor_set(x_52, 8, x_40);
lean_ctor_set(x_52, 9, x_41);
lean_ctor_set(x_52, 10, x_42);
lean_ctor_set(x_52, 11, x_50);
x_53 = lean_st_ref_set(x_1, x_52, x_16);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_7);
x_57 = lean_box(0);
lean_ctor_set(x_8, 0, x_57);
return x_8;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_8, 0);
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_8);
x_60 = lean_ctor_get(x_58, 11);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_isEmpty___rarg(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_62 = lean_st_ref_take(x_1, x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_63, 9);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 10);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 11);
lean_inc(x_76);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 lean_ctor_release(x_63, 7);
 lean_ctor_release(x_63, 8);
 lean_ctor_release(x_63, 9);
 lean_ctor_release(x_63, 10);
 lean_ctor_release(x_63, 11);
 x_77 = x_63;
} else {
 lean_dec_ref(x_63);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_79 = l_Array_back___rarg(x_78, x_76);
x_80 = lean_array_pop(x_76);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_81, x_80, x_79);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 12, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_66);
lean_ctor_set(x_86, 2, x_67);
lean_ctor_set(x_86, 3, x_68);
lean_ctor_set(x_86, 4, x_69);
lean_ctor_set(x_86, 5, x_70);
lean_ctor_set(x_86, 6, x_71);
lean_ctor_set(x_86, 7, x_72);
lean_ctor_set(x_86, 8, x_73);
lean_ctor_set(x_86, 9, x_74);
lean_ctor_set(x_86, 10, x_75);
lean_ctor_set(x_86, 11, x_84);
x_87 = lean_st_ref_set(x_1, x_86, x_64);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_7);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_59);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 10);
x_14 = lean_array_push(x_13, x_1);
lean_ctor_set(x_10, 10, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
x_29 = lean_ctor_get(x_10, 7);
x_30 = lean_ctor_get(x_10, 8);
x_31 = lean_ctor_get(x_10, 9);
x_32 = lean_ctor_get(x_10, 10);
x_33 = lean_ctor_get(x_10, 11);
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
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_34 = lean_array_push(x_32, x_1);
x_35 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_27);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_30);
lean_ctor_set(x_35, 9, x_31);
lean_ctor_set(x_35, 10, x_34);
lean_ctor_set(x_35, 11, x_33);
x_36 = lean_st_ref_set(x_3, x_35, x_11);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushFVarArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Closure_pushLocalDecl(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_inc(x_3);
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_9);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_18);
x_20 = l_Lean_FVarId_getDecl(x_18, x_3, x_4, x_5, x_6, x_17);
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
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 3);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_23, x_24, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Expr_fvar___override(x_18);
x_29 = l_Lean_Meta_Closure_pushFVarArg(x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_21, 2);
x_39 = lean_ctor_get(x_21, 3);
x_40 = lean_ctor_get(x_21, 4);
x_41 = lean_ctor_get(x_21, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = l_Lean_Meta_getZetaDeltaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_44, x_18);
lean_dec(x_44);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_free_object(x_21);
lean_dec(x_40);
x_47 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_38, x_39, x_47, x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Expr_fvar___override(x_18);
x_51 = l_Lean_Meta_Closure_pushFVarArg(x_50, x_1, x_2, x_3, x_4, x_5, x_6, x_49);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_7 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_46);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_Meta_Closure_collectExpr(x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l_Lean_Meta_Closure_collectExpr(x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_take(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_68 = lean_ctor_get(x_65, 7);
x_69 = lean_unsigned_to_nat(0u);
x_70 = 0;
x_71 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_69);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_70);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_71);
x_72 = lean_array_push(x_68, x_21);
lean_ctor_set(x_65, 7, x_72);
x_73 = lean_st_ref_set(x_2, x_65, x_66);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_take(x_2, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_76, 5);
x_80 = lean_array_size(x_79);
x_81 = 0;
x_82 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_80, x_81, x_79);
lean_dec(x_62);
lean_ctor_set(x_76, 5, x_82);
x_83 = lean_st_ref_set(x_2, x_76, x_77);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_7 = x_84;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_86 = lean_ctor_get(x_76, 0);
x_87 = lean_ctor_get(x_76, 1);
x_88 = lean_ctor_get(x_76, 2);
x_89 = lean_ctor_get(x_76, 3);
x_90 = lean_ctor_get(x_76, 4);
x_91 = lean_ctor_get(x_76, 5);
x_92 = lean_ctor_get(x_76, 6);
x_93 = lean_ctor_get(x_76, 7);
x_94 = lean_ctor_get(x_76, 8);
x_95 = lean_ctor_get(x_76, 9);
x_96 = lean_ctor_get(x_76, 10);
x_97 = lean_ctor_get(x_76, 11);
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
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_76);
x_98 = lean_array_size(x_91);
x_99 = 0;
x_100 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_98, x_99, x_91);
lean_dec(x_62);
x_101 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_101, 0, x_86);
lean_ctor_set(x_101, 1, x_87);
lean_ctor_set(x_101, 2, x_88);
lean_ctor_set(x_101, 3, x_89);
lean_ctor_set(x_101, 4, x_90);
lean_ctor_set(x_101, 5, x_100);
lean_ctor_set(x_101, 6, x_92);
lean_ctor_set(x_101, 7, x_93);
lean_ctor_set(x_101, 8, x_94);
lean_ctor_set(x_101, 9, x_95);
lean_ctor_set(x_101, 10, x_96);
lean_ctor_set(x_101, 11, x_97);
x_102 = lean_st_ref_set(x_2, x_101, x_77);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_7 = x_103;
goto _start;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_105 = lean_ctor_get(x_65, 0);
x_106 = lean_ctor_get(x_65, 1);
x_107 = lean_ctor_get(x_65, 2);
x_108 = lean_ctor_get(x_65, 3);
x_109 = lean_ctor_get(x_65, 4);
x_110 = lean_ctor_get(x_65, 5);
x_111 = lean_ctor_get(x_65, 6);
x_112 = lean_ctor_get(x_65, 7);
x_113 = lean_ctor_get(x_65, 8);
x_114 = lean_ctor_get(x_65, 9);
x_115 = lean_ctor_get(x_65, 10);
x_116 = lean_ctor_get(x_65, 11);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_65);
x_117 = lean_unsigned_to_nat(0u);
x_118 = 0;
x_119 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_117);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_118);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_119);
x_120 = lean_array_push(x_112, x_21);
x_121 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_106);
lean_ctor_set(x_121, 2, x_107);
lean_ctor_set(x_121, 3, x_108);
lean_ctor_set(x_121, 4, x_109);
lean_ctor_set(x_121, 5, x_110);
lean_ctor_set(x_121, 6, x_111);
lean_ctor_set(x_121, 7, x_120);
lean_ctor_set(x_121, 8, x_113);
lean_ctor_set(x_121, 9, x_114);
lean_ctor_set(x_121, 10, x_115);
lean_ctor_set(x_121, 11, x_116);
x_122 = lean_st_ref_set(x_2, x_121, x_66);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_take(x_2, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_125, 5);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 6);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 7);
lean_inc(x_134);
x_135 = lean_ctor_get(x_125, 8);
lean_inc(x_135);
x_136 = lean_ctor_get(x_125, 9);
lean_inc(x_136);
x_137 = lean_ctor_get(x_125, 10);
lean_inc(x_137);
x_138 = lean_ctor_get(x_125, 11);
lean_inc(x_138);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 lean_ctor_release(x_125, 6);
 lean_ctor_release(x_125, 7);
 lean_ctor_release(x_125, 8);
 lean_ctor_release(x_125, 9);
 lean_ctor_release(x_125, 10);
 lean_ctor_release(x_125, 11);
 x_139 = x_125;
} else {
 lean_dec_ref(x_125);
 x_139 = lean_box(0);
}
x_140 = lean_array_size(x_132);
x_141 = 0;
x_142 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_140, x_141, x_132);
lean_dec(x_62);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 12, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_127);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set(x_143, 2, x_129);
lean_ctor_set(x_143, 3, x_130);
lean_ctor_set(x_143, 4, x_131);
lean_ctor_set(x_143, 5, x_142);
lean_ctor_set(x_143, 6, x_133);
lean_ctor_set(x_143, 7, x_134);
lean_ctor_set(x_143, 8, x_135);
lean_ctor_set(x_143, 9, x_136);
lean_ctor_set(x_143, 10, x_137);
lean_ctor_set(x_143, 11, x_138);
x_144 = lean_st_ref_set(x_2, x_143, x_126);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_7 = x_145;
goto _start;
}
}
else
{
uint8_t x_147; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_61);
if (x_147 == 0)
{
return x_61;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_61, 0);
x_149 = lean_ctor_get(x_61, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_61);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = !lean_is_exclusive(x_58);
if (x_151 == 0)
{
return x_58;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_58, 0);
x_153 = lean_ctor_get(x_58, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_58);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_21, 2);
x_156 = lean_ctor_get(x_21, 3);
x_157 = lean_ctor_get(x_21, 4);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_21);
x_158 = l_Lean_Meta_getZetaDeltaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_159, x_18);
lean_dec(x_159);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; lean_object* x_163; 
lean_dec(x_157);
x_162 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_163 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_155, x_156, x_162, x_1, x_2, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l_Lean_Expr_fvar___override(x_18);
x_166 = l_Lean_Meta_Closure_pushFVarArg(x_165, x_1, x_2, x_3, x_4, x_5, x_6, x_164);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_7 = x_167;
goto _start;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_171 = x_163;
} else {
 lean_dec_ref(x_163);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; 
lean_dec(x_161);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_173 = l_Lean_Meta_Closure_collectExpr(x_156, x_1, x_2, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_176 = l_Lean_Meta_Closure_collectExpr(x_157, x_1, x_2, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_st_ref_take(x_2, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 5);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 6);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 7);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 8);
lean_inc(x_190);
x_191 = lean_ctor_get(x_180, 9);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 10);
lean_inc(x_192);
x_193 = lean_ctor_get(x_180, 11);
lean_inc(x_193);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 lean_ctor_release(x_180, 6);
 lean_ctor_release(x_180, 7);
 lean_ctor_release(x_180, 8);
 lean_ctor_release(x_180, 9);
 lean_ctor_release(x_180, 10);
 lean_ctor_release(x_180, 11);
 x_194 = x_180;
} else {
 lean_dec_ref(x_180);
 x_194 = lean_box(0);
}
x_195 = lean_unsigned_to_nat(0u);
x_196 = 0;
x_197 = 0;
lean_inc(x_177);
lean_inc(x_19);
x_198 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_19);
lean_ctor_set(x_198, 2, x_155);
lean_ctor_set(x_198, 3, x_174);
lean_ctor_set(x_198, 4, x_177);
lean_ctor_set_uint8(x_198, sizeof(void*)*5, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*5 + 1, x_197);
x_199 = lean_array_push(x_189, x_198);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 12, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_182);
lean_ctor_set(x_200, 1, x_183);
lean_ctor_set(x_200, 2, x_184);
lean_ctor_set(x_200, 3, x_185);
lean_ctor_set(x_200, 4, x_186);
lean_ctor_set(x_200, 5, x_187);
lean_ctor_set(x_200, 6, x_188);
lean_ctor_set(x_200, 7, x_199);
lean_ctor_set(x_200, 8, x_190);
lean_ctor_set(x_200, 9, x_191);
lean_ctor_set(x_200, 10, x_192);
lean_ctor_set(x_200, 11, x_193);
x_201 = lean_st_ref_set(x_2, x_200, x_181);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_st_ref_take(x_2, x_202);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_204, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_204, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_204, 4);
lean_inc(x_210);
x_211 = lean_ctor_get(x_204, 5);
lean_inc(x_211);
x_212 = lean_ctor_get(x_204, 6);
lean_inc(x_212);
x_213 = lean_ctor_get(x_204, 7);
lean_inc(x_213);
x_214 = lean_ctor_get(x_204, 8);
lean_inc(x_214);
x_215 = lean_ctor_get(x_204, 9);
lean_inc(x_215);
x_216 = lean_ctor_get(x_204, 10);
lean_inc(x_216);
x_217 = lean_ctor_get(x_204, 11);
lean_inc(x_217);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 lean_ctor_release(x_204, 2);
 lean_ctor_release(x_204, 3);
 lean_ctor_release(x_204, 4);
 lean_ctor_release(x_204, 5);
 lean_ctor_release(x_204, 6);
 lean_ctor_release(x_204, 7);
 lean_ctor_release(x_204, 8);
 lean_ctor_release(x_204, 9);
 lean_ctor_release(x_204, 10);
 lean_ctor_release(x_204, 11);
 x_218 = x_204;
} else {
 lean_dec_ref(x_204);
 x_218 = lean_box(0);
}
x_219 = lean_array_size(x_211);
x_220 = 0;
x_221 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_177, x_219, x_220, x_211);
lean_dec(x_177);
if (lean_is_scalar(x_218)) {
 x_222 = lean_alloc_ctor(0, 12, 0);
} else {
 x_222 = x_218;
}
lean_ctor_set(x_222, 0, x_206);
lean_ctor_set(x_222, 1, x_207);
lean_ctor_set(x_222, 2, x_208);
lean_ctor_set(x_222, 3, x_209);
lean_ctor_set(x_222, 4, x_210);
lean_ctor_set(x_222, 5, x_221);
lean_ctor_set(x_222, 6, x_212);
lean_ctor_set(x_222, 7, x_213);
lean_ctor_set(x_222, 8, x_214);
lean_ctor_set(x_222, 9, x_215);
lean_ctor_set(x_222, 10, x_216);
lean_ctor_set(x_222, 11, x_217);
x_223 = lean_st_ref_set(x_2, x_222, x_205);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_7 = x_224;
goto _start;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_174);
lean_dec(x_155);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = lean_ctor_get(x_176, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_176, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_228 = x_176;
} else {
 lean_dec_ref(x_176);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_173, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_173, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_232 = x_173;
} else {
 lean_dec_ref(x_173);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_20);
if (x_234 == 0)
{
return x_20;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_20, 0);
x_236 = lean_ctor_get(x_20, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_20);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Closure_process(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_instInhabitedLocalDecl;
x_13 = l_outOfBounds___rarg(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 3);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
lean_dec(x_13);
x_17 = lean_expr_abstract_range(x_15, x_9, x_3);
lean_dec(x_15);
if (x_1 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Expr_forallE___override(x_14, x_17, x_5, x_16);
x_4 = x_9;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Expr_lam___override(x_14, x_17, x_5, x_16);
x_4 = x_9;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 4);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_26 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_27 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_expr_abstract_range(x_23, x_9, x_3);
lean_dec(x_23);
x_30 = lean_expr_abstract_range(x_24, x_9, x_3);
lean_dec(x_24);
x_31 = l_Lean_Expr_letE___override(x_22, x_29, x_30, x_5, x_25);
x_4 = x_9;
x_5 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_2, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
lean_dec(x_33);
x_37 = lean_expr_abstract_range(x_35, x_9, x_3);
lean_dec(x_35);
if (x_1 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Expr_forallE___override(x_34, x_37, x_5, x_36);
x_4 = x_9;
x_5 = x_38;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Expr_lam___override(x_34, x_37, x_5, x_36);
x_4 = x_9;
x_5 = x_40;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_33, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 4);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_33, sizeof(void*)*5);
lean_dec(x_33);
x_46 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_47 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_expr_abstract_range(x_43, x_9, x_3);
lean_dec(x_43);
x_50 = lean_expr_abstract_range(x_44, x_9, x_3);
lean_dec(x_44);
x_51 = l_Lean_Expr_letE___override(x_42, x_49, x_50, x_5, x_45);
x_4 = x_9;
x_5 = x_51;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_array_size(x_2);
x_5 = 0;
lean_inc(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_2);
x_7 = lean_expr_abstract(x_3, x_6);
x_8 = lean_array_get_size(x_2);
x_9 = l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(x_1, x_2, x_6, x_8, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_instInhabitedLocalDecl;
x_12 = l_outOfBounds___rarg(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
lean_dec(x_12);
x_16 = lean_expr_abstract_range(x_14, x_8, x_2);
lean_dec(x_14);
x_17 = l_Lean_Expr_lam___override(x_13, x_16, x_4, x_15);
x_3 = x_8;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 4);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*5);
lean_dec(x_12);
x_23 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_expr_abstract_range(x_20, x_8, x_2);
lean_dec(x_20);
x_27 = lean_expr_abstract_range(x_21, x_8, x_2);
lean_dec(x_21);
x_28 = l_Lean_Expr_letE___override(x_19, x_26, x_27, x_4, x_22);
x_3 = x_8;
x_4 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_array_fget(x_1, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 3);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_30, sizeof(void*)*4);
lean_dec(x_30);
x_34 = lean_expr_abstract_range(x_32, x_8, x_2);
lean_dec(x_32);
x_35 = l_Lean_Expr_lam___override(x_31, x_34, x_4, x_33);
x_3 = x_8;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_30, sizeof(void*)*5);
lean_dec(x_30);
x_41 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_42 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_expr_abstract_range(x_38, x_8, x_2);
lean_dec(x_38);
x_45 = lean_expr_abstract_range(x_39, x_8, x_2);
lean_dec(x_39);
x_46 = l_Lean_Expr_letE___override(x_37, x_44, x_45, x_4, x_40);
x_3 = x_8;
x_4 = x_46;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_size(x_1);
x_4 = 0;
lean_inc(x_1);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_3, x_4, x_1);
x_6 = lean_expr_abstract(x_2, x_5);
x_7 = lean_array_get_size(x_1);
x_8 = l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_5, x_7, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkLambda(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_instInhabitedLocalDecl;
x_12 = l_outOfBounds___rarg(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
lean_dec(x_12);
x_16 = lean_expr_abstract_range(x_14, x_8, x_2);
lean_dec(x_14);
x_17 = l_Lean_Expr_forallE___override(x_13, x_16, x_4, x_15);
x_3 = x_8;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 4);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*5);
lean_dec(x_12);
x_23 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_expr_abstract_range(x_20, x_8, x_2);
lean_dec(x_20);
x_27 = lean_expr_abstract_range(x_21, x_8, x_2);
lean_dec(x_21);
x_28 = l_Lean_Expr_letE___override(x_19, x_26, x_27, x_4, x_22);
x_3 = x_8;
x_4 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_array_fget(x_1, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 3);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_30, sizeof(void*)*4);
lean_dec(x_30);
x_34 = lean_expr_abstract_range(x_32, x_8, x_2);
lean_dec(x_32);
x_35 = l_Lean_Expr_forallE___override(x_31, x_34, x_4, x_33);
x_3 = x_8;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_30, sizeof(void*)*5);
lean_dec(x_30);
x_41 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_42 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_expr_abstract_range(x_38, x_8, x_2);
lean_dec(x_38);
x_45 = lean_expr_abstract_range(x_39, x_8, x_2);
lean_dec(x_39);
x_46 = l_Lean_Expr_letE___override(x_37, x_44, x_45, x_4, x_40);
x_3 = x_8;
x_4 = x_46;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_size(x_1);
x_4 = 0;
lean_inc(x_1);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_3, x_4, x_1);
x_6 = lean_expr_abstract(x_2, x_5);
x_7 = lean_array_get_size(x_1);
x_8 = l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_5, x_7, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkForall(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_resetZetaDeltaFVarIds___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
lean_ctor_set_uint8(x_11, 10, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_20);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_20);
lean_free_object(x_10);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_5);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get_uint8(x_11, 0);
x_43 = lean_ctor_get_uint8(x_11, 1);
x_44 = lean_ctor_get_uint8(x_11, 2);
x_45 = lean_ctor_get_uint8(x_11, 3);
x_46 = lean_ctor_get_uint8(x_11, 4);
x_47 = lean_ctor_get_uint8(x_11, 5);
x_48 = lean_ctor_get_uint8(x_11, 6);
x_49 = lean_ctor_get_uint8(x_11, 7);
x_50 = lean_ctor_get_uint8(x_11, 8);
x_51 = lean_ctor_get_uint8(x_11, 9);
x_52 = lean_ctor_get_uint8(x_11, 11);
x_53 = lean_ctor_get_uint8(x_11, 12);
lean_dec(x_11);
x_54 = 1;
x_55 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_55, 0, x_42);
lean_ctor_set_uint8(x_55, 1, x_43);
lean_ctor_set_uint8(x_55, 2, x_44);
lean_ctor_set_uint8(x_55, 3, x_45);
lean_ctor_set_uint8(x_55, 4, x_46);
lean_ctor_set_uint8(x_55, 5, x_47);
lean_ctor_set_uint8(x_55, 6, x_48);
lean_ctor_set_uint8(x_55, 7, x_49);
lean_ctor_set_uint8(x_55, 8, x_50);
lean_ctor_set_uint8(x_55, 9, x_51);
lean_ctor_set_uint8(x_55, 10, x_54);
lean_ctor_set_uint8(x_55, 11, x_52);
lean_ctor_set_uint8(x_55, 12, x_53);
lean_ctor_set(x_5, 0, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
lean_ctor_set(x_10, 1, x_60);
lean_ctor_set(x_10, 0, x_57);
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_10);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_60);
lean_dec(x_57);
lean_free_object(x_10);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_57);
lean_dec(x_5);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_78 = lean_ctor_get(x_5, 1);
x_79 = lean_ctor_get(x_5, 2);
x_80 = lean_ctor_get(x_5, 3);
x_81 = lean_ctor_get(x_5, 4);
x_82 = lean_ctor_get(x_5, 5);
x_83 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_84 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_85 = lean_ctor_get_uint8(x_11, 0);
x_86 = lean_ctor_get_uint8(x_11, 1);
x_87 = lean_ctor_get_uint8(x_11, 2);
x_88 = lean_ctor_get_uint8(x_11, 3);
x_89 = lean_ctor_get_uint8(x_11, 4);
x_90 = lean_ctor_get_uint8(x_11, 5);
x_91 = lean_ctor_get_uint8(x_11, 6);
x_92 = lean_ctor_get_uint8(x_11, 7);
x_93 = lean_ctor_get_uint8(x_11, 8);
x_94 = lean_ctor_get_uint8(x_11, 9);
x_95 = lean_ctor_get_uint8(x_11, 11);
x_96 = lean_ctor_get_uint8(x_11, 12);
if (lean_is_exclusive(x_11)) {
 x_97 = x_11;
} else {
 lean_dec_ref(x_11);
 x_97 = lean_box(0);
}
x_98 = 1;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 0, 13);
} else {
 x_99 = x_97;
}
lean_ctor_set_uint8(x_99, 0, x_85);
lean_ctor_set_uint8(x_99, 1, x_86);
lean_ctor_set_uint8(x_99, 2, x_87);
lean_ctor_set_uint8(x_99, 3, x_88);
lean_ctor_set_uint8(x_99, 4, x_89);
lean_ctor_set_uint8(x_99, 5, x_90);
lean_ctor_set_uint8(x_99, 6, x_91);
lean_ctor_set_uint8(x_99, 7, x_92);
lean_ctor_set_uint8(x_99, 8, x_93);
lean_ctor_set_uint8(x_99, 9, x_94);
lean_ctor_set_uint8(x_99, 10, x_98);
lean_ctor_set_uint8(x_99, 11, x_95);
lean_ctor_set_uint8(x_99, 12, x_96);
x_100 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_78);
lean_ctor_set(x_100, 2, x_79);
lean_ctor_set(x_100, 3, x_80);
lean_ctor_set(x_100, 4, x_81);
lean_ctor_set(x_100, 5, x_82);
lean_ctor_set_uint8(x_100, sizeof(void*)*6, x_83);
lean_ctor_set_uint8(x_100, sizeof(void*)*6 + 1, x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_100);
x_101 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_100, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_100);
x_104 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_100, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Closure_process(x_3, x_4, x_100, x_6, x_7, x_8, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
lean_ctor_set(x_10, 1, x_105);
lean_ctor_set(x_10, 0, x_102);
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_105);
lean_dec(x_102);
lean_free_object(x_10);
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_102);
lean_dec(x_100);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = lean_ctor_get(x_104, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_117 = x_104;
} else {
 lean_dec_ref(x_104);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_100);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_119 = lean_ctor_get(x_101, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_121 = x_101;
} else {
 lean_dec_ref(x_101);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_123 = lean_ctor_get(x_10, 1);
lean_inc(x_123);
lean_dec(x_10);
x_124 = lean_ctor_get(x_5, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_5, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_5, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_5, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_5, 5);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_130 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_131 = x_5;
} else {
 lean_dec_ref(x_5);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get_uint8(x_11, 0);
x_133 = lean_ctor_get_uint8(x_11, 1);
x_134 = lean_ctor_get_uint8(x_11, 2);
x_135 = lean_ctor_get_uint8(x_11, 3);
x_136 = lean_ctor_get_uint8(x_11, 4);
x_137 = lean_ctor_get_uint8(x_11, 5);
x_138 = lean_ctor_get_uint8(x_11, 6);
x_139 = lean_ctor_get_uint8(x_11, 7);
x_140 = lean_ctor_get_uint8(x_11, 8);
x_141 = lean_ctor_get_uint8(x_11, 9);
x_142 = lean_ctor_get_uint8(x_11, 11);
x_143 = lean_ctor_get_uint8(x_11, 12);
if (lean_is_exclusive(x_11)) {
 x_144 = x_11;
} else {
 lean_dec_ref(x_11);
 x_144 = lean_box(0);
}
x_145 = 1;
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 0, 13);
} else {
 x_146 = x_144;
}
lean_ctor_set_uint8(x_146, 0, x_132);
lean_ctor_set_uint8(x_146, 1, x_133);
lean_ctor_set_uint8(x_146, 2, x_134);
lean_ctor_set_uint8(x_146, 3, x_135);
lean_ctor_set_uint8(x_146, 4, x_136);
lean_ctor_set_uint8(x_146, 5, x_137);
lean_ctor_set_uint8(x_146, 6, x_138);
lean_ctor_set_uint8(x_146, 7, x_139);
lean_ctor_set_uint8(x_146, 8, x_140);
lean_ctor_set_uint8(x_146, 9, x_141);
lean_ctor_set_uint8(x_146, 10, x_145);
lean_ctor_set_uint8(x_146, 11, x_142);
lean_ctor_set_uint8(x_146, 12, x_143);
if (lean_is_scalar(x_131)) {
 x_147 = lean_alloc_ctor(0, 6, 2);
} else {
 x_147 = x_131;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_124);
lean_ctor_set(x_147, 2, x_125);
lean_ctor_set(x_147, 3, x_126);
lean_ctor_set(x_147, 4, x_127);
lean_ctor_set(x_147, 5, x_128);
lean_ctor_set_uint8(x_147, sizeof(void*)*6, x_129);
lean_ctor_set_uint8(x_147, sizeof(void*)*6 + 1, x_130);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_147);
x_148 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_147, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_147);
x_151 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_147, x_6, x_7, x_8, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_Meta_Closure_process(x_3, x_4, x_147, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_152);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_152);
lean_dec(x_149);
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_163 = lean_ctor_get(x_151, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_151, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_165 = x_151;
} else {
 lean_dec_ref(x_151);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_167 = lean_ctor_get(x_148, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_148, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_169 = x_148;
} else {
 lean_dec_ref(x_148);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__3;
x_2 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_2);
lean_ctor_set(x_4, 8, x_3);
lean_ctor_set(x_4, 9, x_2);
lean_ctor_set(x_4, 10, x_2);
lean_ctor_set(x_4, 11, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
x_21 = lean_ctor_get(x_18, 5);
lean_inc(x_21);
x_22 = l_Array_reverse___rarg(x_21);
x_23 = lean_ctor_get(x_18, 6);
lean_inc(x_23);
x_24 = l_Array_append___rarg(x_22, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_18, 7);
lean_inc(x_25);
x_26 = l_Array_reverse___rarg(x_25);
lean_inc(x_26);
x_27 = l_Lean_Meta_Closure_mkForall(x_26, x_19);
lean_dec(x_19);
lean_inc(x_24);
x_28 = l_Lean_Meta_Closure_mkForall(x_24, x_27);
lean_dec(x_27);
x_29 = l_Lean_Meta_Closure_mkLambda(x_26, x_20);
lean_dec(x_20);
x_30 = l_Lean_Meta_Closure_mkLambda(x_24, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_18, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 10);
lean_inc(x_33);
x_34 = l_Array_reverse___rarg(x_33);
x_35 = lean_ctor_get(x_18, 9);
lean_inc(x_35);
lean_dec(x_18);
x_36 = l_Array_append___rarg(x_34, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_32);
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
x_42 = lean_ctor_get(x_38, 5);
lean_inc(x_42);
x_43 = l_Array_reverse___rarg(x_42);
x_44 = lean_ctor_get(x_38, 6);
lean_inc(x_44);
x_45 = l_Array_append___rarg(x_43, x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_38, 7);
lean_inc(x_46);
x_47 = l_Array_reverse___rarg(x_46);
lean_inc(x_47);
x_48 = l_Lean_Meta_Closure_mkForall(x_47, x_40);
lean_dec(x_40);
lean_inc(x_45);
x_49 = l_Lean_Meta_Closure_mkForall(x_45, x_48);
lean_dec(x_48);
x_50 = l_Lean_Meta_Closure_mkLambda(x_47, x_41);
lean_dec(x_41);
x_51 = l_Lean_Meta_Closure_mkLambda(x_45, x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_38, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_38, 10);
lean_inc(x_54);
x_55 = l_Array_reverse___rarg(x_54);
x_56 = lean_ctor_get(x_38, 9);
lean_inc(x_56);
lean_dec(x_38);
x_57 = l_Array_append___rarg(x_55, x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_53);
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
lean_dec(x_3);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = l_Lean_Environment_hasUnsafe(x_14, x_3);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
if (x_15 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Environment_hasUnsafe(x_14, x_4);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_5);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_14);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_28);
x_29 = l_Lean_Environment_hasUnsafe(x_28, x_3);
lean_inc(x_1);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
if (x_29 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Environment_hasUnsafe(x_28, x_4);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 1;
x_35 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_4);
lean_ctor_set(x_35, 2, x_5);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_5);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 2, x_5);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_array_to_list(x_9);
x_11 = l_Lean_Expr_const___override(x_2, x_10);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkAppN(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; uint32_t x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
lean_inc(x_18);
x_19 = l_Lean_getMaxHeight(x_17, x_18);
x_20 = lean_unbox_uint32(x_19);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_uint32_add(x_20, x_21);
x_23 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_23, 0, x_22);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_array_to_list(x_24);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_1);
x_27 = l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_25, x_26, x_18, x_23, x_6, x_7, x_8, x_9, x_16);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_30);
x_31 = l_Lean_addDecl(x_30, x_8, x_9, x_29);
if (lean_obj_tag(x_31) == 0)
{
if (x_5 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_33, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_compileDecl(x_30, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_37, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_37);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkAuxDefinition(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = 1;
x_14 = l_Lean_Meta_mkAuxDefinition(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkAuxDefinitionFor(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_Environment_hasUnsafe(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = l_Lean_Environment_hasUnsafe(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_array_to_list(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_18);
x_25 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_13);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_addDecl(x_27, x_7, x_8, x_16);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_11, 3);
lean_inc(x_31);
x_32 = lean_array_to_list(x_31);
x_33 = l_Lean_Expr_const___override(x_1, x_32);
x_34 = lean_ctor_get(x_11, 4);
lean_inc(x_34);
lean_dec(x_11);
x_35 = l_Lean_mkAppN(x_33, x_34);
lean_dec(x_34);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_11, 3);
lean_inc(x_37);
x_38 = lean_array_to_list(x_37);
x_39 = l_Lean_Expr_const___override(x_1, x_38);
x_40 = lean_ctor_get(x_11, 4);
lean_inc(x_40);
lean_dec(x_11);
x_41 = l_Lean_mkAppN(x_39, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
x_48 = lean_array_to_list(x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_18);
x_50 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_50);
lean_ctor_set(x_13, 0, x_1);
x_51 = lean_box(0);
x_52 = 0;
x_53 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_13);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_addDecl(x_54, x_7, x_8, x_16);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_11, 3);
lean_inc(x_58);
x_59 = lean_array_to_list(x_58);
x_60 = l_Lean_Expr_const___override(x_1, x_59);
x_61 = lean_ctor_get(x_11, 4);
lean_inc(x_61);
lean_dec(x_11);
x_62 = l_Lean_mkAppN(x_60, x_61);
lean_dec(x_61);
lean_ctor_set(x_55, 0, x_62);
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_ctor_get(x_11, 3);
lean_inc(x_64);
x_65 = lean_array_to_list(x_64);
x_66 = l_Lean_Expr_const___override(x_1, x_65);
x_67 = lean_ctor_get(x_11, 4);
lean_inc(x_67);
lean_dec(x_11);
x_68 = l_Lean_mkAppN(x_66, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_11);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_55);
if (x_70 == 0)
{
return x_55;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_55, 0);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_17);
x_74 = lean_ctor_get(x_11, 0);
lean_inc(x_74);
x_75 = lean_array_to_list(x_74);
lean_inc(x_1);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_18);
x_77 = lean_ctor_get(x_11, 2);
lean_inc(x_77);
x_78 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_78);
lean_ctor_set(x_13, 0, x_1);
x_79 = lean_box(0);
x_80 = 0;
x_81 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_13);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_addDecl(x_82, x_7, x_8, x_16);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_11, 3);
lean_inc(x_86);
x_87 = lean_array_to_list(x_86);
x_88 = l_Lean_Expr_const___override(x_1, x_87);
x_89 = lean_ctor_get(x_11, 4);
lean_inc(x_89);
lean_dec(x_11);
x_90 = l_Lean_mkAppN(x_88, x_89);
lean_dec(x_89);
lean_ctor_set(x_83, 0, x_90);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_ctor_get(x_11, 3);
lean_inc(x_92);
x_93 = lean_array_to_list(x_92);
x_94 = l_Lean_Expr_const___override(x_1, x_93);
x_95 = lean_ctor_get(x_11, 4);
lean_inc(x_95);
lean_dec(x_11);
x_96 = l_Lean_mkAppN(x_94, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_11);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_83);
if (x_98 == 0)
{
return x_83;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_83, 0);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_83);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_13, 0);
x_103 = lean_ctor_get(x_13, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_13);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_inc(x_104);
x_106 = l_Lean_Environment_hasUnsafe(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_11, 2);
lean_inc(x_107);
x_108 = l_Lean_Environment_hasUnsafe(x_104, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_11, 0);
lean_inc(x_109);
x_110 = lean_array_to_list(x_109);
lean_inc(x_1);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_105);
x_112 = lean_box(0);
lean_inc(x_1);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_addDecl(x_115, x_7, x_8, x_103);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_11, 3);
lean_inc(x_119);
x_120 = lean_array_to_list(x_119);
x_121 = l_Lean_Expr_const___override(x_1, x_120);
x_122 = lean_ctor_get(x_11, 4);
lean_inc(x_122);
lean_dec(x_11);
x_123 = l_Lean_mkAppN(x_121, x_122);
lean_dec(x_122);
if (lean_is_scalar(x_118)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_118;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_11);
lean_dec(x_1);
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_129 = lean_ctor_get(x_11, 0);
lean_inc(x_129);
x_130 = lean_array_to_list(x_129);
lean_inc(x_1);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_1);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_105);
x_132 = lean_box(0);
lean_inc(x_1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_1);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_box(0);
x_135 = 0;
x_136 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_107);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_addDecl(x_137, x_7, x_8, x_103);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_11, 3);
lean_inc(x_141);
x_142 = lean_array_to_list(x_141);
x_143 = l_Lean_Expr_const___override(x_1, x_142);
x_144 = lean_ctor_get(x_11, 4);
lean_inc(x_144);
lean_dec(x_11);
x_145 = l_Lean_mkAppN(x_143, x_144);
lean_dec(x_144);
if (lean_is_scalar(x_140)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_140;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_139);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_11);
lean_dec(x_1);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_104);
x_151 = lean_ctor_get(x_11, 0);
lean_inc(x_151);
x_152 = lean_array_to_list(x_151);
lean_inc(x_1);
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_105);
x_154 = lean_ctor_get(x_11, 2);
lean_inc(x_154);
x_155 = lean_box(0);
lean_inc(x_1);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_box(0);
x_158 = 0;
x_159 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_159, 0, x_153);
lean_ctor_set(x_159, 1, x_154);
lean_ctor_set(x_159, 2, x_157);
lean_ctor_set(x_159, 3, x_156);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = l_Lean_addDecl(x_160, x_7, x_8, x_103);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_11, 3);
lean_inc(x_164);
x_165 = lean_array_to_list(x_164);
x_166 = l_Lean_Expr_const___override(x_1, x_165);
x_167 = lean_ctor_get(x_11, 4);
lean_inc(x_167);
lean_dec(x_11);
x_168 = l_Lean_mkAppN(x_166, x_167);
lean_dec(x_167);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_163;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_11);
lean_dec(x_1);
x_170 = lean_ctor_get(x_161, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_172 = x_161;
} else {
 lean_dec_ref(x_161);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_10);
if (x_174 == 0)
{
return x_10;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_10, 0);
x_176 = lean_ctor_get(x_10, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_10);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkAuxTheorem(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheoremFor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = l_Lean_Meta_mkAuxTheorem(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheoremFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkAuxTheoremFor(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
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
l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1 = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1);
l_Lean_Meta_Closure_instInhabitedToProcessElement = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement);
l_Lean_Meta_Closure_State_visitedLevel___default___closed__1 = _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default___closed__1);
l_Lean_Meta_Closure_State_visitedLevel___default___closed__2 = _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default___closed__2);
l_Lean_Meta_Closure_State_visitedLevel___default___closed__3 = _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default___closed__3);
l_Lean_Meta_Closure_State_visitedLevel___default = _init_l_Lean_Meta_Closure_State_visitedLevel___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default);
l_Lean_Meta_Closure_State_visitedExpr___default = _init_l_Lean_Meta_Closure_State_visitedExpr___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedExpr___default);
l_Lean_Meta_Closure_State_levelParams___default___closed__1 = _init_l_Lean_Meta_Closure_State_levelParams___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelParams___default___closed__1);
l_Lean_Meta_Closure_State_levelParams___default = _init_l_Lean_Meta_Closure_State_levelParams___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelParams___default);
l_Lean_Meta_Closure_State_nextLevelIdx___default = _init_l_Lean_Meta_Closure_State_nextLevelIdx___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_nextLevelIdx___default);
l_Lean_Meta_Closure_State_levelArgs___default = _init_l_Lean_Meta_Closure_State_levelArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelArgs___default);
l_Lean_Meta_Closure_State_newLocalDecls___default = _init_l_Lean_Meta_Closure_State_newLocalDecls___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLocalDecls___default);
l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default = _init_l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default);
l_Lean_Meta_Closure_State_newLetDecls___default = _init_l_Lean_Meta_Closure_State_newLetDecls___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLetDecls___default);
l_Lean_Meta_Closure_State_nextExprIdx___default = _init_l_Lean_Meta_Closure_State_nextExprIdx___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_nextExprIdx___default);
l_Lean_Meta_Closure_State_exprMVarArgs___default = _init_l_Lean_Meta_Closure_State_exprMVarArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_exprMVarArgs___default);
l_Lean_Meta_Closure_State_exprFVarArgs___default = _init_l_Lean_Meta_Closure_State_exprFVarArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_exprFVarArgs___default);
l_Lean_Meta_Closure_State_toProcess___default = _init_l_Lean_Meta_Closure_State_toProcess___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_toProcess___default);
l_Lean_Meta_Closure_mkNewLevelParam___closed__1 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__1);
l_Lean_Meta_Closure_mkNewLevelParam___closed__2 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__2);
l_Lean_Meta_Closure_collectLevelAux___closed__1 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__1);
l_Lean_Meta_Closure_collectLevelAux___closed__2 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__2);
l_Lean_Meta_Closure_collectLevelAux___closed__3 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__3);
l_Lean_Meta_Closure_collectLevelAux___closed__4 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__4);
l_Lean_Meta_Closure_collectLevelAux___closed__5 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__5);
l_Lean_Meta_Closure_collectLevelAux___closed__6 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__6);
l_Lean_Meta_Closure_collectLevelAux___closed__7 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__7);
l_Lean_Meta_Closure_collectLevelAux___closed__8 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__8);
l_Lean_Meta_Closure_collectLevelAux___closed__9 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__9();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__9);
l_Lean_Meta_Closure_collectLevelAux___closed__10 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__10();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__10);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Meta_Closure_collectExprAux___closed__1 = _init_l_Lean_Meta_Closure_collectExprAux___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__1);
l_Lean_Meta_Closure_collectExprAux___closed__2 = _init_l_Lean_Meta_Closure_collectExprAux___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__2);
l_Lean_Meta_Closure_collectExprAux___closed__3 = _init_l_Lean_Meta_Closure_collectExprAux___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__3);
l_Lean_Meta_Closure_collectExprAux___closed__4 = _init_l_Lean_Meta_Closure_collectExprAux___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__4);
l_Lean_Meta_Closure_collectExprAux___closed__5 = _init_l_Lean_Meta_Closure_collectExprAux___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__5);
l_Lean_Meta_Closure_collectExprAux___closed__6 = _init_l_Lean_Meta_Closure_collectExprAux___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__6);
l_Lean_Meta_Closure_collectExprAux___closed__7 = _init_l_Lean_Meta_Closure_collectExprAux___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__7);
l_Lean_Meta_Closure_collectExprAux___closed__8 = _init_l_Lean_Meta_Closure_collectExprAux___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__8);
l_Lean_Meta_Closure_collectExprAux___closed__9 = _init_l_Lean_Meta_Closure_collectExprAux___closed__9();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__9);
l_Lean_Meta_Closure_collectExprAux___closed__10 = _init_l_Lean_Meta_Closure_collectExprAux___closed__10();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__10);
l_Lean_Meta_Closure_collectExprAux___closed__11 = _init_l_Lean_Meta_Closure_collectExprAux___closed__11();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__11);
l_Lean_Meta_Closure_collectExprAux___closed__12 = _init_l_Lean_Meta_Closure_collectExprAux___closed__12();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__12);
l_Lean_Meta_Closure_collectExprAux___closed__13 = _init_l_Lean_Meta_Closure_collectExprAux___closed__13();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__13);
l_Lean_Meta_Closure_collectExprAux___closed__14 = _init_l_Lean_Meta_Closure_collectExprAux___closed__14();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__14);
l_Lean_Meta_Closure_collectExprAux___closed__15 = _init_l_Lean_Meta_Closure_collectExprAux___closed__15();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__15);
l_Lean_Meta_Closure_collectExprAux___closed__16 = _init_l_Lean_Meta_Closure_collectExprAux___closed__16();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__16);
l_Lean_Meta_Closure_collectExprAux___closed__17 = _init_l_Lean_Meta_Closure_collectExprAux___closed__17();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__17);
l_Lean_Meta_Closure_collectExprAux___closed__18 = _init_l_Lean_Meta_Closure_collectExprAux___closed__18();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__18);
l_Lean_Meta_Closure_collectExprAux___closed__19 = _init_l_Lean_Meta_Closure_collectExprAux___closed__19();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__19);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
