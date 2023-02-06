// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Init Lean.MetavarContext Lean.Environment Lean.Util.FoldConsts Lean.Meta.Basic Lean.Meta.Check
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__8;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__12;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__6;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__14;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_LocalDecl_index(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelParams___default;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__17;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__8;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__7;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__9;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__2;
lean_object* l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_data_hashmap_mk_idx(lean_object*, uint64_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__9;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__15;
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__7;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_data_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Level_hash(x_4);
x_8 = lean_data_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Level_hash(x_12);
x_17 = lean_data_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Level_hash(x_2);
lean_inc(x_7);
x_9 = lean_data_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Level_hash(x_2);
lean_inc(x_23);
x_25 = lean_data_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_93; 
x_93 = l_Lean_Level_hasMVar(x_2);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Level_hasParam(x_2);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = 1;
x_10 = x_95;
goto block_92;
}
else
{
uint8_t x_96; 
x_96 = 0;
x_10 = x_96;
goto block_92;
}
}
else
{
uint8_t x_97; 
x_97 = 0;
x_10 = x_97;
goto block_92;
}
block_92:
{
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_11);
x_17 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_18 = lean_apply_8(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_19);
x_26 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_25, x_2, x_19);
lean_ctor_set(x_22, 0, x_26);
x_27 = lean_st_ref_set(x_4, x_22, x_23);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
x_36 = lean_ctor_get(x_22, 4);
x_37 = lean_ctor_get(x_22, 5);
x_38 = lean_ctor_get(x_22, 6);
x_39 = lean_ctor_get(x_22, 7);
x_40 = lean_ctor_get(x_22, 8);
x_41 = lean_ctor_get(x_22, 9);
x_42 = lean_ctor_get(x_22, 10);
x_43 = lean_ctor_get(x_22, 11);
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
lean_dec(x_22);
lean_inc(x_19);
x_44 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_32, x_2, x_19);
x_45 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_38);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
lean_ctor_set(x_45, 9, x_41);
lean_ctor_set(x_45, 10, x_42);
lean_ctor_set(x_45, 11, x_43);
x_46 = lean_st_ref_set(x_4, x_45, x_23);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_54);
return x_11;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_2);
x_58 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_57, x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_60 = lean_apply_8(x_1, x_2, x_59, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_take(x_4, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 7);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 8);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 9);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 10);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 11);
lean_inc(x_77);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 lean_ctor_release(x_64, 5);
 lean_ctor_release(x_64, 6);
 lean_ctor_release(x_64, 7);
 lean_ctor_release(x_64, 8);
 lean_ctor_release(x_64, 9);
 lean_ctor_release(x_64, 10);
 lean_ctor_release(x_64, 11);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
 x_78 = lean_box(0);
}
lean_inc(x_61);
x_79 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_66, x_2, x_61);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 12, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_67);
lean_ctor_set(x_80, 2, x_68);
lean_ctor_set(x_80, 3, x_69);
lean_ctor_set(x_80, 4, x_70);
lean_ctor_set(x_80, 5, x_71);
lean_ctor_set(x_80, 6, x_72);
lean_ctor_set(x_80, 7, x_73);
lean_ctor_set(x_80, 8, x_74);
lean_ctor_set(x_80, 9, x_75);
lean_ctor_set(x_80, 10, x_76);
lean_ctor_set(x_80, 11, x_77);
x_81 = lean_st_ref_set(x_4, x_80, x_65);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_61);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_4);
lean_dec(x_2);
x_85 = lean_ctor_get(x_60, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_60, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_87 = x_60;
} else {
 lean_dec_ref(x_60);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
lean_dec(x_58);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_56);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set(x_91, 1, x_9);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_1, x_2);
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
uint8_t x_10; uint8_t x_93; 
x_93 = l_Lean_Expr_hasLevelParam(x_2);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasFVar(x_2);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasMVar(x_2);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = 1;
x_10 = x_96;
goto block_92;
}
else
{
uint8_t x_97; 
x_97 = 0;
x_10 = x_97;
goto block_92;
}
}
else
{
uint8_t x_98; 
x_98 = 0;
x_10 = x_98;
goto block_92;
}
}
else
{
uint8_t x_99; 
x_99 = 0;
x_10 = x_99;
goto block_92;
}
block_92:
{
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_11);
x_17 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_18 = lean_apply_8(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_19);
x_26 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_25, x_2, x_19);
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_4, x_22, x_23);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
x_36 = lean_ctor_get(x_22, 4);
x_37 = lean_ctor_get(x_22, 5);
x_38 = lean_ctor_get(x_22, 6);
x_39 = lean_ctor_get(x_22, 7);
x_40 = lean_ctor_get(x_22, 8);
x_41 = lean_ctor_get(x_22, 9);
x_42 = lean_ctor_get(x_22, 10);
x_43 = lean_ctor_get(x_22, 11);
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
lean_dec(x_22);
lean_inc(x_19);
x_44 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_33, x_2, x_19);
x_45 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_38);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
lean_ctor_set(x_45, 9, x_41);
lean_ctor_set(x_45, 10, x_42);
lean_ctor_set(x_45, 11, x_43);
x_46 = lean_st_ref_set(x_4, x_45, x_23);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_54);
return x_11;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_2);
x_58 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_57, x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_60 = lean_apply_8(x_1, x_2, x_59, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_take(x_4, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 7);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 8);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 9);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 10);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 11);
lean_inc(x_77);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 lean_ctor_release(x_64, 5);
 lean_ctor_release(x_64, 6);
 lean_ctor_release(x_64, 7);
 lean_ctor_release(x_64, 8);
 lean_ctor_release(x_64, 9);
 lean_ctor_release(x_64, 10);
 lean_ctor_release(x_64, 11);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
 x_78 = lean_box(0);
}
lean_inc(x_61);
x_79 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_67, x_2, x_61);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 12, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_68);
lean_ctor_set(x_80, 3, x_69);
lean_ctor_set(x_80, 4, x_70);
lean_ctor_set(x_80, 5, x_71);
lean_ctor_set(x_80, 6, x_72);
lean_ctor_set(x_80, 7, x_73);
lean_ctor_set(x_80, 8, x_74);
lean_ctor_set(x_80, 9, x_75);
lean_ctor_set(x_80, 10, x_76);
lean_ctor_set(x_80, 11, x_77);
x_81 = lean_st_ref_set(x_4, x_80, x_65);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_61);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_4);
lean_dec(x_2);
x_85 = lean_ctor_get(x_60, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_60, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_87 = x_60;
} else {
 lean_dec_ref(x_60);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
lean_dec(x_58);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_56);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set(x_91, 1, x_9);
return x_91;
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
x_1 = lean_mk_string_from_bytes("u", 1);
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
x_1 = lean_mk_string_from_bytes("Lean.Level", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateSucc!Impl", 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ level expected", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__2;
x_3 = lean_unsigned_to_nat(534u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateMax!Impl", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("max level expected", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__5;
x_3 = lean_unsigned_to_nat(545u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateIMax!Impl", 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imax level expected", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__8;
x_3 = lean_unsigned_to_nat(556u);
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
lean_object* x_23; uint8_t x_24; uint8_t x_54; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_54 = l_Lean_Level_hasMVar(x_23);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Level_hasParam(x_23);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 1;
x_24 = x_56;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = 0;
x_24 = x_57;
goto block_53;
}
}
else
{
uint8_t x_58; 
x_58 = 0;
x_24 = x_58;
goto block_53;
}
block_53:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_st_ref_get(x_3, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_23);
x_29 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_28, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_23);
x_30 = l_Lean_Meta_Closure_collectLevelAux(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_3, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_inc(x_31);
x_37 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_36, x_23, x_31);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 7);
lean_inc(x_44);
x_45 = lean_ctor_get(x_34, 8);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 9);
lean_inc(x_46);
x_47 = lean_ctor_get(x_34, 10);
lean_inc(x_47);
x_48 = lean_ctor_get(x_34, 11);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_39);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_41);
lean_ctor_set(x_49, 5, x_42);
lean_ctor_set(x_49, 6, x_43);
lean_ctor_set(x_49, 7, x_44);
lean_ctor_set(x_49, 8, x_45);
lean_ctor_set(x_49, 9, x_46);
lean_ctor_set(x_49, 10, x_47);
lean_ctor_set(x_49, 11, x_48);
x_50 = lean_st_ref_set(x_3, x_49, x_35);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_9 = x_31;
x_10 = x_51;
goto block_21;
}
else
{
lean_object* x_52; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_29, 0);
lean_inc(x_52);
lean_dec(x_29);
x_9 = x_52;
x_10 = x_27;
goto block_21;
}
}
else
{
x_9 = x_23;
x_10 = x_8;
goto block_21;
}
}
}
case 2:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_119; uint8_t x_149; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
x_149 = l_Lean_Level_hasMVar(x_59);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Level_hasParam(x_59);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = 1;
x_119 = x_151;
goto block_148;
}
else
{
uint8_t x_152; 
x_152 = 0;
x_119 = x_152;
goto block_148;
}
}
else
{
uint8_t x_153; 
x_153 = 0;
x_119 = x_153;
goto block_148;
}
block_118:
{
lean_object* x_63; lean_object* x_64; uint8_t x_83; uint8_t x_113; 
x_113 = l_Lean_Level_hasMVar(x_60);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_Level_hasParam(x_60);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = 1;
x_83 = x_115;
goto block_112;
}
else
{
uint8_t x_116; 
x_116 = 0;
x_83 = x_116;
goto block_112;
}
}
else
{
uint8_t x_117; 
x_117 = 0;
x_83 = x_117;
goto block_112;
}
block_82:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_68 = lean_ptr_addr(x_61);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_1);
x_70 = l_Lean_mkLevelMax_x27(x_61, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_73 = lean_ptr_addr(x_63);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_75 = l_Lean_mkLevelMax_x27(x_61, x_63);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_64);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Lean_simpLevelMax_x27(x_61, x_63, x_1);
lean_dec(x_1);
lean_dec(x_63);
lean_dec(x_61);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_64);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_1);
x_79 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_80 = l_panic___at_Lean_Level_normalize___spec__1(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
return x_81;
}
}
block_112:
{
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_st_ref_get(x_3, x_62);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_60);
x_88 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_87, x_60);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_inc(x_60);
x_89 = l_Lean_Meta_Closure_collectLevelAux(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_take(x_3, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_inc(x_90);
x_96 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_95, x_60, x_90);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 6);
lean_inc(x_102);
x_103 = lean_ctor_get(x_93, 7);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 8);
lean_inc(x_104);
x_105 = lean_ctor_get(x_93, 9);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 10);
lean_inc(x_106);
x_107 = lean_ctor_get(x_93, 11);
lean_inc(x_107);
lean_dec(x_93);
x_108 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_97);
lean_ctor_set(x_108, 2, x_98);
lean_ctor_set(x_108, 3, x_99);
lean_ctor_set(x_108, 4, x_100);
lean_ctor_set(x_108, 5, x_101);
lean_ctor_set(x_108, 6, x_102);
lean_ctor_set(x_108, 7, x_103);
lean_ctor_set(x_108, 8, x_104);
lean_ctor_set(x_108, 9, x_105);
lean_ctor_set(x_108, 10, x_106);
lean_ctor_set(x_108, 11, x_107);
x_109 = lean_st_ref_set(x_3, x_108, x_94);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_63 = x_90;
x_64 = x_110;
goto block_82;
}
else
{
lean_object* x_111; 
lean_dec(x_60);
x_111 = lean_ctor_get(x_88, 0);
lean_inc(x_111);
lean_dec(x_88);
x_63 = x_111;
x_64 = x_86;
goto block_82;
}
}
else
{
x_63 = x_60;
x_64 = x_62;
goto block_82;
}
}
}
block_148:
{
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_st_ref_get(x_3, x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_59);
x_124 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_123, x_59);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_inc(x_59);
x_125 = l_Lean_Meta_Closure_collectLevelAux(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_122);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_st_ref_take(x_3, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_inc(x_126);
x_132 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_131, x_59, x_126);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 7);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 8);
lean_inc(x_140);
x_141 = lean_ctor_get(x_129, 9);
lean_inc(x_141);
x_142 = lean_ctor_get(x_129, 10);
lean_inc(x_142);
x_143 = lean_ctor_get(x_129, 11);
lean_inc(x_143);
lean_dec(x_129);
x_144 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_133);
lean_ctor_set(x_144, 2, x_134);
lean_ctor_set(x_144, 3, x_135);
lean_ctor_set(x_144, 4, x_136);
lean_ctor_set(x_144, 5, x_137);
lean_ctor_set(x_144, 6, x_138);
lean_ctor_set(x_144, 7, x_139);
lean_ctor_set(x_144, 8, x_140);
lean_ctor_set(x_144, 9, x_141);
lean_ctor_set(x_144, 10, x_142);
lean_ctor_set(x_144, 11, x_143);
x_145 = lean_st_ref_set(x_3, x_144, x_130);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_61 = x_126;
x_62 = x_146;
goto block_118;
}
else
{
lean_object* x_147; 
lean_dec(x_59);
x_147 = lean_ctor_get(x_124, 0);
lean_inc(x_147);
lean_dec(x_124);
x_61 = x_147;
x_62 = x_122;
goto block_118;
}
}
else
{
x_61 = x_59;
x_62 = x_8;
goto block_118;
}
}
}
case 3:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_214; uint8_t x_244; 
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 1);
lean_inc(x_155);
x_244 = l_Lean_Level_hasMVar(x_154);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = l_Lean_Level_hasParam(x_154);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = 1;
x_214 = x_246;
goto block_243;
}
else
{
uint8_t x_247; 
x_247 = 0;
x_214 = x_247;
goto block_243;
}
}
else
{
uint8_t x_248; 
x_248 = 0;
x_214 = x_248;
goto block_243;
}
block_213:
{
lean_object* x_158; lean_object* x_159; uint8_t x_178; uint8_t x_208; 
x_208 = l_Lean_Level_hasMVar(x_155);
if (x_208 == 0)
{
uint8_t x_209; 
x_209 = l_Lean_Level_hasParam(x_155);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = 1;
x_178 = x_210;
goto block_207;
}
else
{
uint8_t x_211; 
x_211 = 0;
x_178 = x_211;
goto block_207;
}
}
else
{
uint8_t x_212; 
x_212 = 0;
x_178 = x_212;
goto block_207;
}
block_177:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc(x_161);
x_162 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_163 = lean_ptr_addr(x_156);
x_164 = lean_usize_dec_eq(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_161);
lean_dec(x_1);
x_165 = l_Lean_mkLevelIMax_x27(x_156, x_158);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
else
{
size_t x_167; size_t x_168; uint8_t x_169; 
x_167 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_168 = lean_ptr_addr(x_158);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_1);
x_170 = l_Lean_mkLevelIMax_x27(x_156, x_158);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Lean_simpLevelIMax_x27(x_156, x_158, x_1);
lean_dec(x_1);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_159);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_1);
x_174 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_175 = l_panic___at_Lean_Level_normalize___spec__1(x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_159);
return x_176;
}
}
block_207:
{
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_st_ref_get(x_3, x_157);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_155);
x_183 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_182, x_155);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_inc(x_155);
x_184 = l_Lean_Meta_Closure_collectLevelAux(x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_181);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_st_ref_take(x_3, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_inc(x_185);
x_191 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_190, x_155, x_185);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_188, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_188, 7);
lean_inc(x_198);
x_199 = lean_ctor_get(x_188, 8);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 9);
lean_inc(x_200);
x_201 = lean_ctor_get(x_188, 10);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 11);
lean_inc(x_202);
lean_dec(x_188);
x_203 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_203, 0, x_191);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_193);
lean_ctor_set(x_203, 3, x_194);
lean_ctor_set(x_203, 4, x_195);
lean_ctor_set(x_203, 5, x_196);
lean_ctor_set(x_203, 6, x_197);
lean_ctor_set(x_203, 7, x_198);
lean_ctor_set(x_203, 8, x_199);
lean_ctor_set(x_203, 9, x_200);
lean_ctor_set(x_203, 10, x_201);
lean_ctor_set(x_203, 11, x_202);
x_204 = lean_st_ref_set(x_3, x_203, x_189);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_158 = x_185;
x_159 = x_205;
goto block_177;
}
else
{
lean_object* x_206; 
lean_dec(x_155);
x_206 = lean_ctor_get(x_183, 0);
lean_inc(x_206);
lean_dec(x_183);
x_158 = x_206;
x_159 = x_181;
goto block_177;
}
}
else
{
x_158 = x_155;
x_159 = x_157;
goto block_177;
}
}
}
block_243:
{
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_st_ref_get(x_3, x_8);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_154);
x_219 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_218, x_154);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_inc(x_154);
x_220 = l_Lean_Meta_Closure_collectLevelAux(x_154, x_2, x_3, x_4, x_5, x_6, x_7, x_217);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_st_ref_take(x_3, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
lean_inc(x_221);
x_227 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_226, x_154, x_221);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 4);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 5);
lean_inc(x_232);
x_233 = lean_ctor_get(x_224, 6);
lean_inc(x_233);
x_234 = lean_ctor_get(x_224, 7);
lean_inc(x_234);
x_235 = lean_ctor_get(x_224, 8);
lean_inc(x_235);
x_236 = lean_ctor_get(x_224, 9);
lean_inc(x_236);
x_237 = lean_ctor_get(x_224, 10);
lean_inc(x_237);
x_238 = lean_ctor_get(x_224, 11);
lean_inc(x_238);
lean_dec(x_224);
x_239 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_239, 0, x_227);
lean_ctor_set(x_239, 1, x_228);
lean_ctor_set(x_239, 2, x_229);
lean_ctor_set(x_239, 3, x_230);
lean_ctor_set(x_239, 4, x_231);
lean_ctor_set(x_239, 5, x_232);
lean_ctor_set(x_239, 6, x_233);
lean_ctor_set(x_239, 7, x_234);
lean_ctor_set(x_239, 8, x_235);
lean_ctor_set(x_239, 9, x_236);
lean_ctor_set(x_239, 10, x_237);
lean_ctor_set(x_239, 11, x_238);
x_240 = lean_st_ref_set(x_3, x_239, x_225);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_156 = x_221;
x_157 = x_241;
goto block_213;
}
else
{
lean_object* x_242; 
lean_dec(x_154);
x_242 = lean_ctor_get(x_219, 0);
lean_inc(x_242);
lean_dec(x_219);
x_156 = x_242;
x_157 = x_217;
goto block_213;
}
}
else
{
x_156 = x_154;
x_157 = x_8;
goto block_213;
}
}
}
default: 
{
lean_object* x_249; 
x_249 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_249;
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
uint8_t x_9; uint8_t x_82; 
x_82 = l_Lean_Level_hasMVar(x_1);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Level_hasParam(x_1);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 1;
x_9 = x_84;
goto block_81;
}
else
{
uint8_t x_85; 
x_85 = 0;
x_9 = x_85;
goto block_81;
}
}
else
{
uint8_t x_86; 
x_86 = 0;
x_9 = x_86;
goto block_81;
}
block_81:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_10);
lean_inc(x_1);
x_16 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_17);
x_24 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_23, x_1, x_17);
lean_ctor_set(x_20, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_17);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
x_32 = lean_ctor_get(x_20, 2);
x_33 = lean_ctor_get(x_20, 3);
x_34 = lean_ctor_get(x_20, 4);
x_35 = lean_ctor_get(x_20, 5);
x_36 = lean_ctor_get(x_20, 6);
x_37 = lean_ctor_get(x_20, 7);
x_38 = lean_ctor_get(x_20, 8);
x_39 = lean_ctor_get(x_20, 9);
x_40 = lean_ctor_get(x_20, 10);
x_41 = lean_ctor_get(x_20, 11);
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
lean_dec(x_20);
lean_inc(x_17);
x_42 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_30, x_1, x_17);
x_43 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_36);
lean_ctor_set(x_43, 7, x_37);
lean_ctor_set(x_43, 8, x_38);
lean_ctor_set(x_43, 9, x_39);
lean_ctor_set(x_43, 10, x_40);
lean_ctor_set(x_43, 11, x_41);
x_44 = lean_st_ref_set(x_3, x_43, x_21);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_48);
return x_10;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_51, x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_1);
x_53 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_3, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 8);
lean_inc(x_67);
x_68 = lean_ctor_get(x_57, 9);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 10);
lean_inc(x_69);
x_70 = lean_ctor_get(x_57, 11);
lean_inc(x_70);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 lean_ctor_release(x_57, 9);
 lean_ctor_release(x_57, 10);
 lean_ctor_release(x_57, 11);
 x_71 = x_57;
} else {
 lean_dec_ref(x_57);
 x_71 = lean_box(0);
}
lean_inc(x_54);
x_72 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_59, x_1, x_54);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 12, 0);
} else {
 x_73 = x_71;
}
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
x_74 = lean_st_ref_set(x_3, x_73, x_58);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_52, 0);
lean_inc(x_78);
lean_dec(x_52);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_50);
return x_79;
}
}
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_8);
return x_80;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_5, x_31, x_20);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_33);
return x_35;
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
x_1 = lean_mk_string_from_bytes("_x", 2);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata expected", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__2;
x_3 = lean_unsigned_to_nat(1503u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__5;
x_3 = lean_unsigned_to_nat(1514u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateApp!Impl", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("application expected", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__8;
x_3 = lean_unsigned_to_nat(1465u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateLambdaE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lambda expected", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__11;
x_3 = lean_unsigned_to_nat(1560u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateForallE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forall expected", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__14;
x_3 = lean_unsigned_to_nat(1540u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateLet!Impl", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let expression expected", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__17;
x_3 = lean_unsigned_to_nat(1569u);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Meta_Closure_pushToProcess(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
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
x_48 = l_Lean_Expr_fvar___override(x_42);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lean_Expr_fvar___override(x_42);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
x_54 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_Closure_pushToProcess(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = l_Lean_Expr_fvar___override(x_55);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = l_Lean_Expr_fvar___override(x_55);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_38);
x_65 = lean_ctor_get(x_39, 1);
lean_inc(x_65);
lean_dec(x_39);
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
lean_dec(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_67 = l_Lean_Meta_Closure_preprocess(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_144; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_144 = l_Lean_Expr_hasLevelParam(x_68);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Expr_hasFVar(x_68);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_68);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = 1;
x_71 = x_147;
goto block_143;
}
else
{
uint8_t x_148; 
x_148 = 0;
x_71 = x_148;
goto block_143;
}
}
else
{
uint8_t x_149; 
x_149 = 0;
x_71 = x_149;
goto block_143;
}
}
else
{
uint8_t x_150; 
x_150 = 0;
x_71 = x_150;
goto block_143;
}
block_143:
{
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_70);
x_72 = lean_st_ref_get(x_3, x_69);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_68);
x_77 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_76, x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_free_object(x_72);
lean_inc(x_68);
x_78 = l_Lean_Meta_Closure_collectExprAux(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_take(x_3, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_79);
x_86 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_85, x_68, x_79);
x_87 = lean_ctor_get(x_82, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 11);
lean_inc(x_96);
lean_dec(x_82);
x_97 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_97, 0, x_84);
lean_ctor_set(x_97, 1, x_86);
lean_ctor_set(x_97, 2, x_87);
lean_ctor_set(x_97, 3, x_88);
lean_ctor_set(x_97, 4, x_89);
lean_ctor_set(x_97, 5, x_90);
lean_ctor_set(x_97, 6, x_91);
lean_ctor_set(x_97, 7, x_92);
lean_ctor_set(x_97, 8, x_93);
lean_ctor_set(x_97, 9, x_94);
lean_ctor_set(x_97, 10, x_95);
lean_ctor_set(x_97, 11, x_96);
x_98 = lean_st_ref_set(x_3, x_97, x_83);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_79);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_79);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_68);
x_103 = !lean_is_exclusive(x_78);
if (x_103 == 0)
{
return x_78;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_78, 0);
x_105 = lean_ctor_get(x_78, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_78);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_107 = lean_ctor_get(x_77, 0);
lean_inc(x_107);
lean_dec(x_77);
lean_ctor_set(x_72, 0, x_107);
return x_72;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_72, 0);
x_109 = lean_ctor_get(x_72, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_72);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_68);
x_111 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_110, x_68);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_inc(x_68);
x_112 = l_Lean_Meta_Closure_collectExprAux(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_st_ref_take(x_3, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_inc(x_113);
x_120 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_119, x_68, x_113);
x_121 = lean_ctor_get(x_116, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 5);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 6);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 7);
lean_inc(x_126);
x_127 = lean_ctor_get(x_116, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 9);
lean_inc(x_128);
x_129 = lean_ctor_get(x_116, 10);
lean_inc(x_129);
x_130 = lean_ctor_get(x_116, 11);
lean_inc(x_130);
lean_dec(x_116);
x_131 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set(x_131, 2, x_121);
lean_ctor_set(x_131, 3, x_122);
lean_ctor_set(x_131, 4, x_123);
lean_ctor_set(x_131, 5, x_124);
lean_ctor_set(x_131, 6, x_125);
lean_ctor_set(x_131, 7, x_126);
lean_ctor_set(x_131, 8, x_127);
lean_ctor_set(x_131, 9, x_128);
lean_ctor_set(x_131, 10, x_129);
lean_ctor_set(x_131, 11, x_130);
x_132 = lean_st_ref_set(x_3, x_131, x_117);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_68);
x_136 = lean_ctor_get(x_112, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_112, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_138 = x_112;
} else {
 lean_dec_ref(x_112);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = lean_ctor_get(x_111, 0);
lean_inc(x_140);
lean_dec(x_111);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_109);
return x_141;
}
}
}
else
{
lean_object* x_142; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_70)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_70;
}
lean_ctor_set(x_142, 0, x_68);
lean_ctor_set(x_142, 1, x_69);
return x_142;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_151 = !lean_is_exclusive(x_67);
if (x_151 == 0)
{
return x_67;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_67, 0);
x_153 = lean_ctor_get(x_67, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_67);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_155 = !lean_is_exclusive(x_39);
if (x_155 == 0)
{
return x_39;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_39, 0);
x_157 = lean_ctor_get(x_39, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_39);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
case 2:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = l_Lean_MVarId_getDecl(x_159, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 2);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_164 = l_Lean_Meta_Closure_preprocess(x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_205; uint8_t x_239; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_239 = l_Lean_Expr_hasLevelParam(x_165);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = l_Lean_Expr_hasFVar(x_165);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Expr_hasMVar(x_165);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = 1;
x_205 = x_242;
goto block_238;
}
else
{
uint8_t x_243; 
x_243 = 0;
x_205 = x_243;
goto block_238;
}
}
else
{
uint8_t x_244; 
x_244 = 0;
x_205 = x_244;
goto block_238;
}
}
else
{
uint8_t x_245; 
x_245 = 0;
x_205 = x_245;
goto block_238;
}
block_204:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_169 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_st_ref_take(x_3, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_176, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_176, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 5);
lean_inc(x_183);
x_184 = lean_ctor_get(x_176, 6);
lean_inc(x_184);
x_185 = lean_unsigned_to_nat(0u);
x_186 = 0;
x_187 = 0;
lean_inc(x_170);
x_188 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_170);
lean_ctor_set(x_188, 2, x_173);
lean_ctor_set(x_188, 3, x_167);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4 + 1, x_187);
x_189 = lean_array_push(x_184, x_188);
x_190 = lean_ctor_get(x_176, 7);
lean_inc(x_190);
x_191 = lean_ctor_get(x_176, 8);
lean_inc(x_191);
x_192 = lean_ctor_get(x_176, 9);
lean_inc(x_192);
x_193 = lean_array_push(x_192, x_1);
x_194 = lean_ctor_get(x_176, 10);
lean_inc(x_194);
x_195 = lean_ctor_get(x_176, 11);
lean_inc(x_195);
lean_dec(x_176);
x_196 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_196, 0, x_178);
lean_ctor_set(x_196, 1, x_179);
lean_ctor_set(x_196, 2, x_180);
lean_ctor_set(x_196, 3, x_181);
lean_ctor_set(x_196, 4, x_182);
lean_ctor_set(x_196, 5, x_183);
lean_ctor_set(x_196, 6, x_189);
lean_ctor_set(x_196, 7, x_190);
lean_ctor_set(x_196, 8, x_191);
lean_ctor_set(x_196, 9, x_193);
lean_ctor_set(x_196, 10, x_194);
lean_ctor_set(x_196, 11, x_195);
x_197 = lean_st_ref_set(x_3, x_196, x_177);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_197, 0);
lean_dec(x_199);
x_200 = l_Lean_Expr_fvar___override(x_170);
lean_ctor_set(x_197, 0, x_200);
return x_197;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
lean_dec(x_197);
x_202 = l_Lean_Expr_fvar___override(x_170);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
block_238:
{
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_st_ref_get(x_3, x_166);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_165);
x_210 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_209, x_165);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_165);
x_211 = l_Lean_Meta_Closure_collectExprAux(x_165, x_2, x_3, x_4, x_5, x_6, x_7, x_208);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_st_ref_take(x_3, x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_inc(x_212);
x_219 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_218, x_165, x_212);
x_220 = lean_ctor_get(x_215, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_215, 5);
lean_inc(x_223);
x_224 = lean_ctor_get(x_215, 6);
lean_inc(x_224);
x_225 = lean_ctor_get(x_215, 7);
lean_inc(x_225);
x_226 = lean_ctor_get(x_215, 8);
lean_inc(x_226);
x_227 = lean_ctor_get(x_215, 9);
lean_inc(x_227);
x_228 = lean_ctor_get(x_215, 10);
lean_inc(x_228);
x_229 = lean_ctor_get(x_215, 11);
lean_inc(x_229);
lean_dec(x_215);
x_230 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_230, 0, x_217);
lean_ctor_set(x_230, 1, x_219);
lean_ctor_set(x_230, 2, x_220);
lean_ctor_set(x_230, 3, x_221);
lean_ctor_set(x_230, 4, x_222);
lean_ctor_set(x_230, 5, x_223);
lean_ctor_set(x_230, 6, x_224);
lean_ctor_set(x_230, 7, x_225);
lean_ctor_set(x_230, 8, x_226);
lean_ctor_set(x_230, 9, x_227);
lean_ctor_set(x_230, 10, x_228);
lean_ctor_set(x_230, 11, x_229);
x_231 = lean_st_ref_set(x_3, x_230, x_216);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_167 = x_212;
x_168 = x_232;
goto block_204;
}
else
{
uint8_t x_233; 
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_211);
if (x_233 == 0)
{
return x_211;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_211, 0);
x_235 = lean_ctor_get(x_211, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_211);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_165);
x_237 = lean_ctor_get(x_210, 0);
lean_inc(x_237);
lean_dec(x_210);
x_167 = x_237;
x_168 = x_208;
goto block_204;
}
}
else
{
x_167 = x_165;
x_168 = x_166;
goto block_204;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_164);
if (x_246 == 0)
{
return x_164;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_164, 0);
x_248 = lean_ctor_get(x_164, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_164);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_160);
if (x_250 == 0)
{
return x_160;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_160, 0);
x_252 = lean_ctor_get(x_160, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_160);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
case 3:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
lean_inc(x_254);
x_255 = l_Lean_Meta_Closure_collectLevel(x_254, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; size_t x_258; size_t x_259; uint8_t x_260; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_259 = lean_ptr_addr(x_257);
x_260 = lean_usize_dec_eq(x_258, x_259);
if (x_260 == 0)
{
lean_object* x_261; 
lean_dec(x_1);
x_261 = l_Lean_Expr_sort___override(x_257);
lean_ctor_set(x_255, 0, x_261);
return x_255;
}
else
{
lean_dec(x_257);
lean_ctor_set(x_255, 0, x_1);
return x_255;
}
}
else
{
lean_object* x_262; lean_object* x_263; size_t x_264; size_t x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_255, 0);
x_263 = lean_ctor_get(x_255, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_255);
x_264 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_265 = lean_ptr_addr(x_262);
x_266 = lean_usize_dec_eq(x_264, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_1);
x_267 = l_Lean_Expr_sort___override(x_262);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_263);
return x_268;
}
else
{
lean_object* x_269; 
lean_dec(x_262);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_1);
lean_ctor_set(x_269, 1, x_263);
return x_269;
}
}
}
case 4:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_270 = lean_ctor_get(x_1, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
x_272 = lean_box(0);
lean_inc(x_271);
x_273 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_271, x_272, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = l_ptrEqList___rarg(x_271, x_275);
lean_dec(x_271);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_1);
x_277 = l_Lean_Expr_const___override(x_270, x_275);
lean_ctor_set(x_273, 0, x_277);
return x_273;
}
else
{
lean_dec(x_275);
lean_dec(x_270);
lean_ctor_set(x_273, 0, x_1);
return x_273;
}
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_278 = lean_ctor_get(x_273, 0);
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_273);
x_280 = l_ptrEqList___rarg(x_271, x_278);
lean_dec(x_271);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_1);
x_281 = l_Lean_Expr_const___override(x_270, x_278);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
else
{
lean_object* x_283; 
lean_dec(x_278);
lean_dec(x_270);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_1);
lean_ctor_set(x_283, 1, x_279);
return x_283;
}
}
}
case 5:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_349; uint8_t x_383; 
x_284 = lean_ctor_get(x_1, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_1, 1);
lean_inc(x_285);
x_383 = l_Lean_Expr_hasLevelParam(x_284);
if (x_383 == 0)
{
uint8_t x_384; 
x_384 = l_Lean_Expr_hasFVar(x_284);
if (x_384 == 0)
{
uint8_t x_385; 
x_385 = l_Lean_Expr_hasMVar(x_284);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = 1;
x_349 = x_386;
goto block_382;
}
else
{
uint8_t x_387; 
x_387 = 0;
x_349 = x_387;
goto block_382;
}
}
else
{
uint8_t x_388; 
x_388 = 0;
x_349 = x_388;
goto block_382;
}
}
else
{
uint8_t x_389; 
x_389 = 0;
x_349 = x_389;
goto block_382;
}
block_348:
{
lean_object* x_288; lean_object* x_289; uint8_t x_307; uint8_t x_341; 
x_341 = l_Lean_Expr_hasLevelParam(x_285);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = l_Lean_Expr_hasFVar(x_285);
if (x_342 == 0)
{
uint8_t x_343; 
x_343 = l_Lean_Expr_hasMVar(x_285);
if (x_343 == 0)
{
uint8_t x_344; 
x_344 = 1;
x_307 = x_344;
goto block_340;
}
else
{
uint8_t x_345; 
x_345 = 0;
x_307 = x_345;
goto block_340;
}
}
else
{
uint8_t x_346; 
x_346 = 0;
x_307 = x_346;
goto block_340;
}
}
else
{
uint8_t x_347; 
x_347 = 0;
x_307 = x_347;
goto block_340;
}
block_306:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_290; lean_object* x_291; size_t x_292; size_t x_293; uint8_t x_294; 
x_290 = lean_ctor_get(x_1, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_1, 1);
lean_inc(x_291);
x_292 = lean_ptr_addr(x_290);
lean_dec(x_290);
x_293 = lean_ptr_addr(x_286);
x_294 = lean_usize_dec_eq(x_292, x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_291);
lean_dec(x_1);
x_295 = l_Lean_Expr_app___override(x_286, x_288);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_289);
return x_296;
}
else
{
size_t x_297; size_t x_298; uint8_t x_299; 
x_297 = lean_ptr_addr(x_291);
lean_dec(x_291);
x_298 = lean_ptr_addr(x_288);
x_299 = lean_usize_dec_eq(x_297, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_1);
x_300 = l_Lean_Expr_app___override(x_286, x_288);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_289);
return x_301;
}
else
{
lean_object* x_302; 
lean_dec(x_288);
lean_dec(x_286);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_1);
lean_ctor_set(x_302, 1, x_289);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_288);
lean_dec(x_286);
lean_dec(x_1);
x_303 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_304 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_289);
return x_305;
}
}
block_340:
{
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_st_ref_get(x_3, x_287);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_285);
x_312 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_311, x_285);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
lean_inc(x_285);
x_313 = l_Lean_Meta_Closure_collectExprAux(x_285, x_2, x_3, x_4, x_5, x_6, x_7, x_310);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_st_ref_take(x_3, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_inc(x_314);
x_321 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_320, x_285, x_314);
x_322 = lean_ctor_get(x_317, 2);
lean_inc(x_322);
x_323 = lean_ctor_get(x_317, 3);
lean_inc(x_323);
x_324 = lean_ctor_get(x_317, 4);
lean_inc(x_324);
x_325 = lean_ctor_get(x_317, 5);
lean_inc(x_325);
x_326 = lean_ctor_get(x_317, 6);
lean_inc(x_326);
x_327 = lean_ctor_get(x_317, 7);
lean_inc(x_327);
x_328 = lean_ctor_get(x_317, 8);
lean_inc(x_328);
x_329 = lean_ctor_get(x_317, 9);
lean_inc(x_329);
x_330 = lean_ctor_get(x_317, 10);
lean_inc(x_330);
x_331 = lean_ctor_get(x_317, 11);
lean_inc(x_331);
lean_dec(x_317);
x_332 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_332, 0, x_319);
lean_ctor_set(x_332, 1, x_321);
lean_ctor_set(x_332, 2, x_322);
lean_ctor_set(x_332, 3, x_323);
lean_ctor_set(x_332, 4, x_324);
lean_ctor_set(x_332, 5, x_325);
lean_ctor_set(x_332, 6, x_326);
lean_ctor_set(x_332, 7, x_327);
lean_ctor_set(x_332, 8, x_328);
lean_ctor_set(x_332, 9, x_329);
lean_ctor_set(x_332, 10, x_330);
lean_ctor_set(x_332, 11, x_331);
x_333 = lean_st_ref_set(x_3, x_332, x_318);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_288 = x_314;
x_289 = x_334;
goto block_306;
}
else
{
uint8_t x_335; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_313);
if (x_335 == 0)
{
return x_313;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_313, 0);
x_337 = lean_ctor_get(x_313, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_313);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
else
{
lean_object* x_339; 
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_339 = lean_ctor_get(x_312, 0);
lean_inc(x_339);
lean_dec(x_312);
x_288 = x_339;
x_289 = x_310;
goto block_306;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_288 = x_285;
x_289 = x_287;
goto block_306;
}
}
}
block_382:
{
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_350 = lean_st_ref_get(x_3, x_8);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
lean_inc(x_284);
x_354 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_353, x_284);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_284);
x_355 = l_Lean_Meta_Closure_collectExprAux(x_284, x_2, x_3, x_4, x_5, x_6, x_7, x_352);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_st_ref_take(x_3, x_357);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_inc(x_356);
x_363 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_362, x_284, x_356);
x_364 = lean_ctor_get(x_359, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_359, 3);
lean_inc(x_365);
x_366 = lean_ctor_get(x_359, 4);
lean_inc(x_366);
x_367 = lean_ctor_get(x_359, 5);
lean_inc(x_367);
x_368 = lean_ctor_get(x_359, 6);
lean_inc(x_368);
x_369 = lean_ctor_get(x_359, 7);
lean_inc(x_369);
x_370 = lean_ctor_get(x_359, 8);
lean_inc(x_370);
x_371 = lean_ctor_get(x_359, 9);
lean_inc(x_371);
x_372 = lean_ctor_get(x_359, 10);
lean_inc(x_372);
x_373 = lean_ctor_get(x_359, 11);
lean_inc(x_373);
lean_dec(x_359);
x_374 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_374, 0, x_361);
lean_ctor_set(x_374, 1, x_363);
lean_ctor_set(x_374, 2, x_364);
lean_ctor_set(x_374, 3, x_365);
lean_ctor_set(x_374, 4, x_366);
lean_ctor_set(x_374, 5, x_367);
lean_ctor_set(x_374, 6, x_368);
lean_ctor_set(x_374, 7, x_369);
lean_ctor_set(x_374, 8, x_370);
lean_ctor_set(x_374, 9, x_371);
lean_ctor_set(x_374, 10, x_372);
lean_ctor_set(x_374, 11, x_373);
x_375 = lean_st_ref_set(x_3, x_374, x_360);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_286 = x_356;
x_287 = x_376;
goto block_348;
}
else
{
uint8_t x_377; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_355);
if (x_377 == 0)
{
return x_355;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_355, 0);
x_379 = lean_ctor_get(x_355, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_355);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
lean_object* x_381; 
lean_dec(x_284);
x_381 = lean_ctor_get(x_354, 0);
lean_inc(x_381);
lean_dec(x_354);
x_286 = x_381;
x_287 = x_352;
goto block_348;
}
}
else
{
x_286 = x_284;
x_287 = x_8;
goto block_348;
}
}
}
case 6:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_461; uint8_t x_495; 
x_390 = lean_ctor_get(x_1, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_1, 2);
lean_inc(x_391);
x_495 = l_Lean_Expr_hasLevelParam(x_390);
if (x_495 == 0)
{
uint8_t x_496; 
x_496 = l_Lean_Expr_hasFVar(x_390);
if (x_496 == 0)
{
uint8_t x_497; 
x_497 = l_Lean_Expr_hasMVar(x_390);
if (x_497 == 0)
{
uint8_t x_498; 
x_498 = 1;
x_461 = x_498;
goto block_494;
}
else
{
uint8_t x_499; 
x_499 = 0;
x_461 = x_499;
goto block_494;
}
}
else
{
uint8_t x_500; 
x_500 = 0;
x_461 = x_500;
goto block_494;
}
}
else
{
uint8_t x_501; 
x_501 = 0;
x_461 = x_501;
goto block_494;
}
block_460:
{
lean_object* x_394; lean_object* x_395; uint8_t x_419; uint8_t x_453; 
x_453 = l_Lean_Expr_hasLevelParam(x_391);
if (x_453 == 0)
{
uint8_t x_454; 
x_454 = l_Lean_Expr_hasFVar(x_391);
if (x_454 == 0)
{
uint8_t x_455; 
x_455 = l_Lean_Expr_hasMVar(x_391);
if (x_455 == 0)
{
uint8_t x_456; 
x_456 = 1;
x_419 = x_456;
goto block_452;
}
else
{
uint8_t x_457; 
x_457 = 0;
x_419 = x_457;
goto block_452;
}
}
else
{
uint8_t x_458; 
x_458 = 0;
x_419 = x_458;
goto block_452;
}
}
else
{
uint8_t x_459; 
x_459 = 0;
x_419 = x_459;
goto block_452;
}
block_418:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; size_t x_401; size_t x_402; uint8_t x_403; 
x_396 = lean_ctor_get(x_1, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_1, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_1, 2);
lean_inc(x_398);
x_399 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
x_400 = l_Lean_Expr_lam___override(x_396, x_397, x_398, x_399);
x_401 = lean_ptr_addr(x_397);
lean_dec(x_397);
x_402 = lean_ptr_addr(x_392);
x_403 = lean_usize_dec_eq(x_401, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_400);
lean_dec(x_398);
x_404 = l_Lean_Expr_lam___override(x_396, x_392, x_394, x_399);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_395);
return x_405;
}
else
{
size_t x_406; size_t x_407; uint8_t x_408; 
x_406 = lean_ptr_addr(x_398);
lean_dec(x_398);
x_407 = lean_ptr_addr(x_394);
x_408 = lean_usize_dec_eq(x_406, x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_400);
x_409 = l_Lean_Expr_lam___override(x_396, x_392, x_394, x_399);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_395);
return x_410;
}
else
{
uint8_t x_411; 
x_411 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_399, x_399);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_400);
x_412 = l_Lean_Expr_lam___override(x_396, x_392, x_394, x_399);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_395);
return x_413;
}
else
{
lean_object* x_414; 
lean_dec(x_396);
lean_dec(x_394);
lean_dec(x_392);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_400);
lean_ctor_set(x_414, 1, x_395);
return x_414;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_394);
lean_dec(x_392);
lean_dec(x_1);
x_415 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_416 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_415);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_395);
return x_417;
}
}
block_452:
{
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_st_ref_get(x_3, x_393);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
lean_inc(x_391);
x_424 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_423, x_391);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
lean_inc(x_391);
x_425 = l_Lean_Meta_Closure_collectExprAux(x_391, x_2, x_3, x_4, x_5, x_6, x_7, x_422);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
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
lean_inc(x_426);
x_433 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_432, x_391, x_426);
x_434 = lean_ctor_get(x_429, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_429, 3);
lean_inc(x_435);
x_436 = lean_ctor_get(x_429, 4);
lean_inc(x_436);
x_437 = lean_ctor_get(x_429, 5);
lean_inc(x_437);
x_438 = lean_ctor_get(x_429, 6);
lean_inc(x_438);
x_439 = lean_ctor_get(x_429, 7);
lean_inc(x_439);
x_440 = lean_ctor_get(x_429, 8);
lean_inc(x_440);
x_441 = lean_ctor_get(x_429, 9);
lean_inc(x_441);
x_442 = lean_ctor_get(x_429, 10);
lean_inc(x_442);
x_443 = lean_ctor_get(x_429, 11);
lean_inc(x_443);
lean_dec(x_429);
x_444 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_444, 0, x_431);
lean_ctor_set(x_444, 1, x_433);
lean_ctor_set(x_444, 2, x_434);
lean_ctor_set(x_444, 3, x_435);
lean_ctor_set(x_444, 4, x_436);
lean_ctor_set(x_444, 5, x_437);
lean_ctor_set(x_444, 6, x_438);
lean_ctor_set(x_444, 7, x_439);
lean_ctor_set(x_444, 8, x_440);
lean_ctor_set(x_444, 9, x_441);
lean_ctor_set(x_444, 10, x_442);
lean_ctor_set(x_444, 11, x_443);
x_445 = lean_st_ref_set(x_3, x_444, x_430);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_394 = x_426;
x_395 = x_446;
goto block_418;
}
else
{
uint8_t x_447; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_425);
if (x_447 == 0)
{
return x_425;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_425, 0);
x_449 = lean_ctor_get(x_425, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_425);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; 
lean_dec(x_391);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_451 = lean_ctor_get(x_424, 0);
lean_inc(x_451);
lean_dec(x_424);
x_394 = x_451;
x_395 = x_422;
goto block_418;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_394 = x_391;
x_395 = x_393;
goto block_418;
}
}
}
block_494:
{
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_st_ref_get(x_3, x_8);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_390);
x_466 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_465, x_390);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_390);
x_467 = l_Lean_Meta_Closure_collectExprAux(x_390, x_2, x_3, x_4, x_5, x_6, x_7, x_464);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_st_ref_take(x_3, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_inc(x_468);
x_475 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_474, x_390, x_468);
x_476 = lean_ctor_get(x_471, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_471, 3);
lean_inc(x_477);
x_478 = lean_ctor_get(x_471, 4);
lean_inc(x_478);
x_479 = lean_ctor_get(x_471, 5);
lean_inc(x_479);
x_480 = lean_ctor_get(x_471, 6);
lean_inc(x_480);
x_481 = lean_ctor_get(x_471, 7);
lean_inc(x_481);
x_482 = lean_ctor_get(x_471, 8);
lean_inc(x_482);
x_483 = lean_ctor_get(x_471, 9);
lean_inc(x_483);
x_484 = lean_ctor_get(x_471, 10);
lean_inc(x_484);
x_485 = lean_ctor_get(x_471, 11);
lean_inc(x_485);
lean_dec(x_471);
x_486 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_486, 0, x_473);
lean_ctor_set(x_486, 1, x_475);
lean_ctor_set(x_486, 2, x_476);
lean_ctor_set(x_486, 3, x_477);
lean_ctor_set(x_486, 4, x_478);
lean_ctor_set(x_486, 5, x_479);
lean_ctor_set(x_486, 6, x_480);
lean_ctor_set(x_486, 7, x_481);
lean_ctor_set(x_486, 8, x_482);
lean_ctor_set(x_486, 9, x_483);
lean_ctor_set(x_486, 10, x_484);
lean_ctor_set(x_486, 11, x_485);
x_487 = lean_st_ref_set(x_3, x_486, x_472);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
x_392 = x_468;
x_393 = x_488;
goto block_460;
}
else
{
uint8_t x_489; 
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_467);
if (x_489 == 0)
{
return x_467;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_467, 0);
x_491 = lean_ctor_get(x_467, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_467);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
lean_object* x_493; 
lean_dec(x_390);
x_493 = lean_ctor_get(x_466, 0);
lean_inc(x_493);
lean_dec(x_466);
x_392 = x_493;
x_393 = x_464;
goto block_460;
}
}
else
{
x_392 = x_390;
x_393 = x_8;
goto block_460;
}
}
}
case 7:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_573; uint8_t x_607; 
x_502 = lean_ctor_get(x_1, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_1, 2);
lean_inc(x_503);
x_607 = l_Lean_Expr_hasLevelParam(x_502);
if (x_607 == 0)
{
uint8_t x_608; 
x_608 = l_Lean_Expr_hasFVar(x_502);
if (x_608 == 0)
{
uint8_t x_609; 
x_609 = l_Lean_Expr_hasMVar(x_502);
if (x_609 == 0)
{
uint8_t x_610; 
x_610 = 1;
x_573 = x_610;
goto block_606;
}
else
{
uint8_t x_611; 
x_611 = 0;
x_573 = x_611;
goto block_606;
}
}
else
{
uint8_t x_612; 
x_612 = 0;
x_573 = x_612;
goto block_606;
}
}
else
{
uint8_t x_613; 
x_613 = 0;
x_573 = x_613;
goto block_606;
}
block_572:
{
lean_object* x_506; lean_object* x_507; uint8_t x_531; uint8_t x_565; 
x_565 = l_Lean_Expr_hasLevelParam(x_503);
if (x_565 == 0)
{
uint8_t x_566; 
x_566 = l_Lean_Expr_hasFVar(x_503);
if (x_566 == 0)
{
uint8_t x_567; 
x_567 = l_Lean_Expr_hasMVar(x_503);
if (x_567 == 0)
{
uint8_t x_568; 
x_568 = 1;
x_531 = x_568;
goto block_564;
}
else
{
uint8_t x_569; 
x_569 = 0;
x_531 = x_569;
goto block_564;
}
}
else
{
uint8_t x_570; 
x_570 = 0;
x_531 = x_570;
goto block_564;
}
}
else
{
uint8_t x_571; 
x_571 = 0;
x_531 = x_571;
goto block_564;
}
block_530:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; size_t x_513; size_t x_514; uint8_t x_515; 
x_508 = lean_ctor_get(x_1, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_1, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_1, 2);
lean_inc(x_510);
x_511 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_510);
lean_inc(x_509);
lean_inc(x_508);
x_512 = l_Lean_Expr_forallE___override(x_508, x_509, x_510, x_511);
x_513 = lean_ptr_addr(x_509);
lean_dec(x_509);
x_514 = lean_ptr_addr(x_504);
x_515 = lean_usize_dec_eq(x_513, x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_512);
lean_dec(x_510);
x_516 = l_Lean_Expr_forallE___override(x_508, x_504, x_506, x_511);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_507);
return x_517;
}
else
{
size_t x_518; size_t x_519; uint8_t x_520; 
x_518 = lean_ptr_addr(x_510);
lean_dec(x_510);
x_519 = lean_ptr_addr(x_506);
x_520 = lean_usize_dec_eq(x_518, x_519);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_512);
x_521 = l_Lean_Expr_forallE___override(x_508, x_504, x_506, x_511);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_507);
return x_522;
}
else
{
uint8_t x_523; 
x_523 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_511, x_511);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; 
lean_dec(x_512);
x_524 = l_Lean_Expr_forallE___override(x_508, x_504, x_506, x_511);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_507);
return x_525;
}
else
{
lean_object* x_526; 
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_504);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_512);
lean_ctor_set(x_526, 1, x_507);
return x_526;
}
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_1);
x_527 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_528 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_527);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_507);
return x_529;
}
}
block_564:
{
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_532 = lean_st_ref_get(x_3, x_505);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_503);
x_536 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_535, x_503);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; 
lean_inc(x_503);
x_537 = l_Lean_Meta_Closure_collectExprAux(x_503, x_2, x_3, x_4, x_5, x_6, x_7, x_534);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_st_ref_take(x_3, x_539);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_inc(x_538);
x_545 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_544, x_503, x_538);
x_546 = lean_ctor_get(x_541, 2);
lean_inc(x_546);
x_547 = lean_ctor_get(x_541, 3);
lean_inc(x_547);
x_548 = lean_ctor_get(x_541, 4);
lean_inc(x_548);
x_549 = lean_ctor_get(x_541, 5);
lean_inc(x_549);
x_550 = lean_ctor_get(x_541, 6);
lean_inc(x_550);
x_551 = lean_ctor_get(x_541, 7);
lean_inc(x_551);
x_552 = lean_ctor_get(x_541, 8);
lean_inc(x_552);
x_553 = lean_ctor_get(x_541, 9);
lean_inc(x_553);
x_554 = lean_ctor_get(x_541, 10);
lean_inc(x_554);
x_555 = lean_ctor_get(x_541, 11);
lean_inc(x_555);
lean_dec(x_541);
x_556 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_556, 0, x_543);
lean_ctor_set(x_556, 1, x_545);
lean_ctor_set(x_556, 2, x_546);
lean_ctor_set(x_556, 3, x_547);
lean_ctor_set(x_556, 4, x_548);
lean_ctor_set(x_556, 5, x_549);
lean_ctor_set(x_556, 6, x_550);
lean_ctor_set(x_556, 7, x_551);
lean_ctor_set(x_556, 8, x_552);
lean_ctor_set(x_556, 9, x_553);
lean_ctor_set(x_556, 10, x_554);
lean_ctor_set(x_556, 11, x_555);
x_557 = lean_st_ref_set(x_3, x_556, x_542);
x_558 = lean_ctor_get(x_557, 1);
lean_inc(x_558);
lean_dec(x_557);
x_506 = x_538;
x_507 = x_558;
goto block_530;
}
else
{
uint8_t x_559; 
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_1);
x_559 = !lean_is_exclusive(x_537);
if (x_559 == 0)
{
return x_537;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_537, 0);
x_561 = lean_ctor_get(x_537, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_537);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
else
{
lean_object* x_563; 
lean_dec(x_503);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_563 = lean_ctor_get(x_536, 0);
lean_inc(x_563);
lean_dec(x_536);
x_506 = x_563;
x_507 = x_534;
goto block_530;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_506 = x_503;
x_507 = x_505;
goto block_530;
}
}
}
block_606:
{
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_574 = lean_st_ref_get(x_3, x_8);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
lean_inc(x_502);
x_578 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_577, x_502);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_502);
x_579 = l_Lean_Meta_Closure_collectExprAux(x_502, x_2, x_3, x_4, x_5, x_6, x_7, x_576);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = lean_st_ref_take(x_3, x_581);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 1);
lean_inc(x_586);
lean_inc(x_580);
x_587 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_586, x_502, x_580);
x_588 = lean_ctor_get(x_583, 2);
lean_inc(x_588);
x_589 = lean_ctor_get(x_583, 3);
lean_inc(x_589);
x_590 = lean_ctor_get(x_583, 4);
lean_inc(x_590);
x_591 = lean_ctor_get(x_583, 5);
lean_inc(x_591);
x_592 = lean_ctor_get(x_583, 6);
lean_inc(x_592);
x_593 = lean_ctor_get(x_583, 7);
lean_inc(x_593);
x_594 = lean_ctor_get(x_583, 8);
lean_inc(x_594);
x_595 = lean_ctor_get(x_583, 9);
lean_inc(x_595);
x_596 = lean_ctor_get(x_583, 10);
lean_inc(x_596);
x_597 = lean_ctor_get(x_583, 11);
lean_inc(x_597);
lean_dec(x_583);
x_598 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_598, 0, x_585);
lean_ctor_set(x_598, 1, x_587);
lean_ctor_set(x_598, 2, x_588);
lean_ctor_set(x_598, 3, x_589);
lean_ctor_set(x_598, 4, x_590);
lean_ctor_set(x_598, 5, x_591);
lean_ctor_set(x_598, 6, x_592);
lean_ctor_set(x_598, 7, x_593);
lean_ctor_set(x_598, 8, x_594);
lean_ctor_set(x_598, 9, x_595);
lean_ctor_set(x_598, 10, x_596);
lean_ctor_set(x_598, 11, x_597);
x_599 = lean_st_ref_set(x_3, x_598, x_584);
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
lean_dec(x_599);
x_504 = x_580;
x_505 = x_600;
goto block_572;
}
else
{
uint8_t x_601; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_601 = !lean_is_exclusive(x_579);
if (x_601 == 0)
{
return x_579;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_579, 0);
x_603 = lean_ctor_get(x_579, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_579);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
else
{
lean_object* x_605; 
lean_dec(x_502);
x_605 = lean_ctor_get(x_578, 0);
lean_inc(x_605);
lean_dec(x_578);
x_504 = x_605;
x_505 = x_576;
goto block_572;
}
}
else
{
x_504 = x_502;
x_505 = x_8;
goto block_572;
}
}
}
case 8:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_732; uint8_t x_766; 
x_614 = lean_ctor_get(x_1, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_1, 2);
lean_inc(x_615);
x_616 = lean_ctor_get(x_1, 3);
lean_inc(x_616);
x_766 = l_Lean_Expr_hasLevelParam(x_614);
if (x_766 == 0)
{
uint8_t x_767; 
x_767 = l_Lean_Expr_hasFVar(x_614);
if (x_767 == 0)
{
uint8_t x_768; 
x_768 = l_Lean_Expr_hasMVar(x_614);
if (x_768 == 0)
{
uint8_t x_769; 
x_769 = 1;
x_732 = x_769;
goto block_765;
}
else
{
uint8_t x_770; 
x_770 = 0;
x_732 = x_770;
goto block_765;
}
}
else
{
uint8_t x_771; 
x_771 = 0;
x_732 = x_771;
goto block_765;
}
}
else
{
uint8_t x_772; 
x_772 = 0;
x_732 = x_772;
goto block_765;
}
block_731:
{
lean_object* x_619; lean_object* x_620; uint8_t x_690; uint8_t x_724; 
x_724 = l_Lean_Expr_hasLevelParam(x_615);
if (x_724 == 0)
{
uint8_t x_725; 
x_725 = l_Lean_Expr_hasFVar(x_615);
if (x_725 == 0)
{
uint8_t x_726; 
x_726 = l_Lean_Expr_hasMVar(x_615);
if (x_726 == 0)
{
uint8_t x_727; 
x_727 = 1;
x_690 = x_727;
goto block_723;
}
else
{
uint8_t x_728; 
x_728 = 0;
x_690 = x_728;
goto block_723;
}
}
else
{
uint8_t x_729; 
x_729 = 0;
x_690 = x_729;
goto block_723;
}
}
else
{
uint8_t x_730; 
x_730 = 0;
x_690 = x_730;
goto block_723;
}
block_689:
{
lean_object* x_621; lean_object* x_622; uint8_t x_648; uint8_t x_682; 
x_682 = l_Lean_Expr_hasLevelParam(x_616);
if (x_682 == 0)
{
uint8_t x_683; 
x_683 = l_Lean_Expr_hasFVar(x_616);
if (x_683 == 0)
{
uint8_t x_684; 
x_684 = l_Lean_Expr_hasMVar(x_616);
if (x_684 == 0)
{
uint8_t x_685; 
x_685 = 1;
x_648 = x_685;
goto block_681;
}
else
{
uint8_t x_686; 
x_686 = 0;
x_648 = x_686;
goto block_681;
}
}
else
{
uint8_t x_687; 
x_687 = 0;
x_648 = x_687;
goto block_681;
}
}
else
{
uint8_t x_688; 
x_688 = 0;
x_648 = x_688;
goto block_681;
}
block_647:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; size_t x_628; size_t x_629; uint8_t x_630; 
x_623 = lean_ctor_get(x_1, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_1, 1);
lean_inc(x_624);
x_625 = lean_ctor_get(x_1, 2);
lean_inc(x_625);
x_626 = lean_ctor_get(x_1, 3);
lean_inc(x_626);
x_627 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_628 = lean_ptr_addr(x_624);
lean_dec(x_624);
x_629 = lean_ptr_addr(x_617);
x_630 = lean_usize_dec_eq(x_628, x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_1);
x_631 = l_Lean_Expr_letE___override(x_623, x_617, x_619, x_621, x_627);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_622);
return x_632;
}
else
{
size_t x_633; size_t x_634; uint8_t x_635; 
x_633 = lean_ptr_addr(x_625);
lean_dec(x_625);
x_634 = lean_ptr_addr(x_619);
x_635 = lean_usize_dec_eq(x_633, x_634);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_626);
lean_dec(x_1);
x_636 = l_Lean_Expr_letE___override(x_623, x_617, x_619, x_621, x_627);
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_622);
return x_637;
}
else
{
size_t x_638; size_t x_639; uint8_t x_640; 
x_638 = lean_ptr_addr(x_626);
lean_dec(x_626);
x_639 = lean_ptr_addr(x_621);
x_640 = lean_usize_dec_eq(x_638, x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_1);
x_641 = l_Lean_Expr_letE___override(x_623, x_617, x_619, x_621, x_627);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_622);
return x_642;
}
else
{
lean_object* x_643; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_617);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_1);
lean_ctor_set(x_643, 1, x_622);
return x_643;
}
}
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_617);
lean_dec(x_1);
x_644 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_645 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_644);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_622);
return x_646;
}
}
block_681:
{
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_649 = lean_st_ref_get(x_3, x_620);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
lean_inc(x_616);
x_653 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_652, x_616);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; 
lean_inc(x_616);
x_654 = l_Lean_Meta_Closure_collectExprAux(x_616, x_2, x_3, x_4, x_5, x_6, x_7, x_651);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = lean_st_ref_take(x_3, x_656);
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_ctor_get(x_658, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_658, 1);
lean_inc(x_661);
lean_inc(x_655);
x_662 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_661, x_616, x_655);
x_663 = lean_ctor_get(x_658, 2);
lean_inc(x_663);
x_664 = lean_ctor_get(x_658, 3);
lean_inc(x_664);
x_665 = lean_ctor_get(x_658, 4);
lean_inc(x_665);
x_666 = lean_ctor_get(x_658, 5);
lean_inc(x_666);
x_667 = lean_ctor_get(x_658, 6);
lean_inc(x_667);
x_668 = lean_ctor_get(x_658, 7);
lean_inc(x_668);
x_669 = lean_ctor_get(x_658, 8);
lean_inc(x_669);
x_670 = lean_ctor_get(x_658, 9);
lean_inc(x_670);
x_671 = lean_ctor_get(x_658, 10);
lean_inc(x_671);
x_672 = lean_ctor_get(x_658, 11);
lean_inc(x_672);
lean_dec(x_658);
x_673 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_673, 0, x_660);
lean_ctor_set(x_673, 1, x_662);
lean_ctor_set(x_673, 2, x_663);
lean_ctor_set(x_673, 3, x_664);
lean_ctor_set(x_673, 4, x_665);
lean_ctor_set(x_673, 5, x_666);
lean_ctor_set(x_673, 6, x_667);
lean_ctor_set(x_673, 7, x_668);
lean_ctor_set(x_673, 8, x_669);
lean_ctor_set(x_673, 9, x_670);
lean_ctor_set(x_673, 10, x_671);
lean_ctor_set(x_673, 11, x_672);
x_674 = lean_st_ref_set(x_3, x_673, x_659);
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
x_621 = x_655;
x_622 = x_675;
goto block_647;
}
else
{
uint8_t x_676; 
lean_dec(x_619);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_1);
x_676 = !lean_is_exclusive(x_654);
if (x_676 == 0)
{
return x_654;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_654, 0);
x_678 = lean_ctor_get(x_654, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_654);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
else
{
lean_object* x_680; 
lean_dec(x_616);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_680 = lean_ctor_get(x_653, 0);
lean_inc(x_680);
lean_dec(x_653);
x_621 = x_680;
x_622 = x_651;
goto block_647;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_621 = x_616;
x_622 = x_620;
goto block_647;
}
}
}
block_723:
{
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_691 = lean_st_ref_get(x_3, x_618);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
lean_inc(x_615);
x_695 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_694, x_615);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_615);
x_696 = l_Lean_Meta_Closure_collectExprAux(x_615, x_2, x_3, x_4, x_5, x_6, x_7, x_693);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_st_ref_take(x_3, x_698);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_700, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_700, 1);
lean_inc(x_703);
lean_inc(x_697);
x_704 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_703, x_615, x_697);
x_705 = lean_ctor_get(x_700, 2);
lean_inc(x_705);
x_706 = lean_ctor_get(x_700, 3);
lean_inc(x_706);
x_707 = lean_ctor_get(x_700, 4);
lean_inc(x_707);
x_708 = lean_ctor_get(x_700, 5);
lean_inc(x_708);
x_709 = lean_ctor_get(x_700, 6);
lean_inc(x_709);
x_710 = lean_ctor_get(x_700, 7);
lean_inc(x_710);
x_711 = lean_ctor_get(x_700, 8);
lean_inc(x_711);
x_712 = lean_ctor_get(x_700, 9);
lean_inc(x_712);
x_713 = lean_ctor_get(x_700, 10);
lean_inc(x_713);
x_714 = lean_ctor_get(x_700, 11);
lean_inc(x_714);
lean_dec(x_700);
x_715 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_715, 0, x_702);
lean_ctor_set(x_715, 1, x_704);
lean_ctor_set(x_715, 2, x_705);
lean_ctor_set(x_715, 3, x_706);
lean_ctor_set(x_715, 4, x_707);
lean_ctor_set(x_715, 5, x_708);
lean_ctor_set(x_715, 6, x_709);
lean_ctor_set(x_715, 7, x_710);
lean_ctor_set(x_715, 8, x_711);
lean_ctor_set(x_715, 9, x_712);
lean_ctor_set(x_715, 10, x_713);
lean_ctor_set(x_715, 11, x_714);
x_716 = lean_st_ref_set(x_3, x_715, x_701);
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
lean_dec(x_716);
x_619 = x_697;
x_620 = x_717;
goto block_689;
}
else
{
uint8_t x_718; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_718 = !lean_is_exclusive(x_696);
if (x_718 == 0)
{
return x_696;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_696, 0);
x_720 = lean_ctor_get(x_696, 1);
lean_inc(x_720);
lean_inc(x_719);
lean_dec(x_696);
x_721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
return x_721;
}
}
}
else
{
lean_object* x_722; 
lean_dec(x_615);
x_722 = lean_ctor_get(x_695, 0);
lean_inc(x_722);
lean_dec(x_695);
x_619 = x_722;
x_620 = x_693;
goto block_689;
}
}
else
{
x_619 = x_615;
x_620 = x_618;
goto block_689;
}
}
}
block_765:
{
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_733 = lean_st_ref_get(x_3, x_8);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
lean_inc(x_614);
x_737 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_736, x_614);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_614);
x_738 = l_Lean_Meta_Closure_collectExprAux(x_614, x_2, x_3, x_4, x_5, x_6, x_7, x_735);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_st_ref_take(x_3, x_740);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_ctor_get(x_742, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_742, 1);
lean_inc(x_745);
lean_inc(x_739);
x_746 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_745, x_614, x_739);
x_747 = lean_ctor_get(x_742, 2);
lean_inc(x_747);
x_748 = lean_ctor_get(x_742, 3);
lean_inc(x_748);
x_749 = lean_ctor_get(x_742, 4);
lean_inc(x_749);
x_750 = lean_ctor_get(x_742, 5);
lean_inc(x_750);
x_751 = lean_ctor_get(x_742, 6);
lean_inc(x_751);
x_752 = lean_ctor_get(x_742, 7);
lean_inc(x_752);
x_753 = lean_ctor_get(x_742, 8);
lean_inc(x_753);
x_754 = lean_ctor_get(x_742, 9);
lean_inc(x_754);
x_755 = lean_ctor_get(x_742, 10);
lean_inc(x_755);
x_756 = lean_ctor_get(x_742, 11);
lean_inc(x_756);
lean_dec(x_742);
x_757 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_757, 0, x_744);
lean_ctor_set(x_757, 1, x_746);
lean_ctor_set(x_757, 2, x_747);
lean_ctor_set(x_757, 3, x_748);
lean_ctor_set(x_757, 4, x_749);
lean_ctor_set(x_757, 5, x_750);
lean_ctor_set(x_757, 6, x_751);
lean_ctor_set(x_757, 7, x_752);
lean_ctor_set(x_757, 8, x_753);
lean_ctor_set(x_757, 9, x_754);
lean_ctor_set(x_757, 10, x_755);
lean_ctor_set(x_757, 11, x_756);
x_758 = lean_st_ref_set(x_3, x_757, x_743);
x_759 = lean_ctor_get(x_758, 1);
lean_inc(x_759);
lean_dec(x_758);
x_617 = x_739;
x_618 = x_759;
goto block_731;
}
else
{
uint8_t x_760; 
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_760 = !lean_is_exclusive(x_738);
if (x_760 == 0)
{
return x_738;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_761 = lean_ctor_get(x_738, 0);
x_762 = lean_ctor_get(x_738, 1);
lean_inc(x_762);
lean_inc(x_761);
lean_dec(x_738);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_761);
lean_ctor_set(x_763, 1, x_762);
return x_763;
}
}
}
else
{
lean_object* x_764; 
lean_dec(x_614);
x_764 = lean_ctor_get(x_737, 0);
lean_inc(x_764);
lean_dec(x_737);
x_617 = x_764;
x_618 = x_735;
goto block_731;
}
}
else
{
x_617 = x_614;
x_618 = x_8;
goto block_731;
}
}
}
case 10:
{
lean_object* x_773; uint8_t x_774; uint8_t x_808; 
x_773 = lean_ctor_get(x_1, 1);
lean_inc(x_773);
x_808 = l_Lean_Expr_hasLevelParam(x_773);
if (x_808 == 0)
{
uint8_t x_809; 
x_809 = l_Lean_Expr_hasFVar(x_773);
if (x_809 == 0)
{
uint8_t x_810; 
x_810 = l_Lean_Expr_hasMVar(x_773);
if (x_810 == 0)
{
uint8_t x_811; 
x_811 = 1;
x_774 = x_811;
goto block_807;
}
else
{
uint8_t x_812; 
x_812 = 0;
x_774 = x_812;
goto block_807;
}
}
else
{
uint8_t x_813; 
x_813 = 0;
x_774 = x_813;
goto block_807;
}
}
else
{
uint8_t x_814; 
x_814 = 0;
x_774 = x_814;
goto block_807;
}
block_807:
{
if (x_774 == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_775 = lean_st_ref_get(x_3, x_8);
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
lean_inc(x_773);
x_779 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_778, x_773);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; 
lean_inc(x_773);
x_780 = l_Lean_Meta_Closure_collectExprAux(x_773, x_2, x_3, x_4, x_5, x_6, x_7, x_777);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = lean_st_ref_take(x_3, x_782);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_786 = lean_ctor_get(x_784, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_787);
lean_inc(x_781);
x_788 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_787, x_773, x_781);
x_789 = lean_ctor_get(x_784, 2);
lean_inc(x_789);
x_790 = lean_ctor_get(x_784, 3);
lean_inc(x_790);
x_791 = lean_ctor_get(x_784, 4);
lean_inc(x_791);
x_792 = lean_ctor_get(x_784, 5);
lean_inc(x_792);
x_793 = lean_ctor_get(x_784, 6);
lean_inc(x_793);
x_794 = lean_ctor_get(x_784, 7);
lean_inc(x_794);
x_795 = lean_ctor_get(x_784, 8);
lean_inc(x_795);
x_796 = lean_ctor_get(x_784, 9);
lean_inc(x_796);
x_797 = lean_ctor_get(x_784, 10);
lean_inc(x_797);
x_798 = lean_ctor_get(x_784, 11);
lean_inc(x_798);
lean_dec(x_784);
x_799 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_799, 0, x_786);
lean_ctor_set(x_799, 1, x_788);
lean_ctor_set(x_799, 2, x_789);
lean_ctor_set(x_799, 3, x_790);
lean_ctor_set(x_799, 4, x_791);
lean_ctor_set(x_799, 5, x_792);
lean_ctor_set(x_799, 6, x_793);
lean_ctor_set(x_799, 7, x_794);
lean_ctor_set(x_799, 8, x_795);
lean_ctor_set(x_799, 9, x_796);
lean_ctor_set(x_799, 10, x_797);
lean_ctor_set(x_799, 11, x_798);
x_800 = lean_st_ref_set(x_3, x_799, x_785);
x_801 = lean_ctor_get(x_800, 1);
lean_inc(x_801);
lean_dec(x_800);
x_9 = x_781;
x_10 = x_801;
goto block_22;
}
else
{
uint8_t x_802; 
lean_dec(x_773);
lean_dec(x_1);
x_802 = !lean_is_exclusive(x_780);
if (x_802 == 0)
{
return x_780;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_780, 0);
x_804 = lean_ctor_get(x_780, 1);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_780);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
return x_805;
}
}
}
else
{
lean_object* x_806; 
lean_dec(x_773);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_806 = lean_ctor_get(x_779, 0);
lean_inc(x_806);
lean_dec(x_779);
x_9 = x_806;
x_10 = x_777;
goto block_22;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_773;
x_10 = x_8;
goto block_22;
}
}
}
case 11:
{
lean_object* x_815; uint8_t x_816; uint8_t x_850; 
x_815 = lean_ctor_get(x_1, 2);
lean_inc(x_815);
x_850 = l_Lean_Expr_hasLevelParam(x_815);
if (x_850 == 0)
{
uint8_t x_851; 
x_851 = l_Lean_Expr_hasFVar(x_815);
if (x_851 == 0)
{
uint8_t x_852; 
x_852 = l_Lean_Expr_hasMVar(x_815);
if (x_852 == 0)
{
uint8_t x_853; 
x_853 = 1;
x_816 = x_853;
goto block_849;
}
else
{
uint8_t x_854; 
x_854 = 0;
x_816 = x_854;
goto block_849;
}
}
else
{
uint8_t x_855; 
x_855 = 0;
x_816 = x_855;
goto block_849;
}
}
else
{
uint8_t x_856; 
x_856 = 0;
x_816 = x_856;
goto block_849;
}
block_849:
{
if (x_816 == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_817 = lean_st_ref_get(x_3, x_8);
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
lean_dec(x_817);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
lean_inc(x_815);
x_821 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_820, x_815);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; 
lean_inc(x_815);
x_822 = l_Lean_Meta_Closure_collectExprAux(x_815, x_2, x_3, x_4, x_5, x_6, x_7, x_819);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = lean_st_ref_take(x_3, x_824);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_826, 1);
lean_inc(x_829);
lean_inc(x_823);
x_830 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_829, x_815, x_823);
x_831 = lean_ctor_get(x_826, 2);
lean_inc(x_831);
x_832 = lean_ctor_get(x_826, 3);
lean_inc(x_832);
x_833 = lean_ctor_get(x_826, 4);
lean_inc(x_833);
x_834 = lean_ctor_get(x_826, 5);
lean_inc(x_834);
x_835 = lean_ctor_get(x_826, 6);
lean_inc(x_835);
x_836 = lean_ctor_get(x_826, 7);
lean_inc(x_836);
x_837 = lean_ctor_get(x_826, 8);
lean_inc(x_837);
x_838 = lean_ctor_get(x_826, 9);
lean_inc(x_838);
x_839 = lean_ctor_get(x_826, 10);
lean_inc(x_839);
x_840 = lean_ctor_get(x_826, 11);
lean_inc(x_840);
lean_dec(x_826);
x_841 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_841, 0, x_828);
lean_ctor_set(x_841, 1, x_830);
lean_ctor_set(x_841, 2, x_831);
lean_ctor_set(x_841, 3, x_832);
lean_ctor_set(x_841, 4, x_833);
lean_ctor_set(x_841, 5, x_834);
lean_ctor_set(x_841, 6, x_835);
lean_ctor_set(x_841, 7, x_836);
lean_ctor_set(x_841, 8, x_837);
lean_ctor_set(x_841, 9, x_838);
lean_ctor_set(x_841, 10, x_839);
lean_ctor_set(x_841, 11, x_840);
x_842 = lean_st_ref_set(x_3, x_841, x_827);
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
lean_dec(x_842);
x_23 = x_823;
x_24 = x_843;
goto block_37;
}
else
{
uint8_t x_844; 
lean_dec(x_815);
lean_dec(x_1);
x_844 = !lean_is_exclusive(x_822);
if (x_844 == 0)
{
return x_822;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_822, 0);
x_846 = lean_ctor_get(x_822, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_822);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
else
{
lean_object* x_848; 
lean_dec(x_815);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_848 = lean_ctor_get(x_821, 0);
lean_inc(x_848);
lean_dec(x_821);
x_23 = x_848;
x_24 = x_819;
goto block_37;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = x_815;
x_24 = x_8;
goto block_37;
}
}
}
default: 
{
lean_object* x_857; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_1);
lean_ctor_set(x_857, 1, x_8);
return x_857;
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
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
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
x_35 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_34);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_94; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_94 = l_Lean_Expr_hasLevelParam(x_10);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasFVar(x_10);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Expr_hasMVar(x_10);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_13 = x_97;
goto block_93;
}
else
{
uint8_t x_98; 
x_98 = 0;
x_13 = x_98;
goto block_93;
}
}
else
{
uint8_t x_99; 
x_99 = 0;
x_13 = x_99;
goto block_93;
}
}
else
{
uint8_t x_100; 
x_100 = 0;
x_13 = x_100;
goto block_93;
}
block_93:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_10);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_18, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_inc(x_10);
x_20 = l_Lean_Meta_Closure_collectExprAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_21);
x_28 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_27, x_10, x_21);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 4);
x_39 = lean_ctor_get(x_24, 5);
x_40 = lean_ctor_get(x_24, 6);
x_41 = lean_ctor_get(x_24, 7);
x_42 = lean_ctor_get(x_24, 8);
x_43 = lean_ctor_get(x_24, 9);
x_44 = lean_ctor_get(x_24, 10);
x_45 = lean_ctor_get(x_24, 11);
lean_inc(x_45);
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
lean_dec(x_24);
lean_inc(x_21);
x_46 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_35, x_10, x_21);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_38);
lean_ctor_set(x_47, 5, x_39);
lean_ctor_set(x_47, 6, x_40);
lean_ctor_set(x_47, 7, x_41);
lean_ctor_set(x_47, 8, x_42);
lean_ctor_set(x_47, 9, x_43);
lean_ctor_set(x_47, 10, x_44);
lean_ctor_set(x_47, 11, x_45);
x_48 = lean_st_ref_set(x_3, x_47, x_25);
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
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_56);
return x_14;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_10);
x_60 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_59, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_inc(x_10);
x_61 = l_Lean_Meta_Closure_collectExprAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_take(x_3, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 7);
lean_inc(x_74);
x_75 = lean_ctor_get(x_65, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 9);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 10);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 11);
lean_inc(x_78);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 lean_ctor_release(x_65, 9);
 lean_ctor_release(x_65, 10);
 lean_ctor_release(x_65, 11);
 x_79 = x_65;
} else {
 lean_dec_ref(x_65);
 x_79 = lean_box(0);
}
lean_inc(x_62);
x_80 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_68, x_10, x_62);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 12, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_70);
lean_ctor_set(x_81, 4, x_71);
lean_ctor_set(x_81, 5, x_72);
lean_ctor_set(x_81, 6, x_73);
lean_ctor_set(x_81, 7, x_74);
lean_ctor_set(x_81, 8, x_75);
lean_ctor_set(x_81, 9, x_76);
lean_ctor_set(x_81, 10, x_77);
lean_ctor_set(x_81, 11, x_78);
x_82 = lean_st_ref_set(x_3, x_81, x_66);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_62);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_10);
x_86 = lean_ctor_get(x_61, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_88 = x_61;
} else {
 lean_dec_ref(x_61);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_60, 0);
lean_inc(x_90);
lean_dec(x_60);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_58);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_12)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_12;
}
lean_ctor_set(x_92, 0, x_10);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_9);
if (x_101 == 0)
{
return x_9;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_9, 0);
x_103 = lean_ctor_get(x_9, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_9);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_159; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_21, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_21, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 x_40 = x_21;
} else {
 lean_dec_ref(x_21);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_159 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2(x_42, x_18);
lean_dec(x_42);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = 1;
x_44 = x_160;
goto block_158;
}
else
{
uint8_t x_161; 
lean_dec(x_159);
x_161 = 0;
x_44 = x_161;
goto block_158;
}
block_158:
{
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Meta_Closure_collectExpr(x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_Closure_collectExpr(x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_take(x_2, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_ctor_get(x_52, 7);
x_56 = lean_unsigned_to_nat(0u);
x_57 = 0;
x_58 = 0;
lean_inc(x_49);
lean_inc(x_19);
if (lean_is_scalar(x_40)) {
 x_59 = lean_alloc_ctor(1, 5, 2);
} else {
 x_59 = x_40;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_19);
lean_ctor_set(x_59, 2, x_37);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_49);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_58);
x_60 = lean_array_push(x_55, x_59);
lean_ctor_set(x_52, 7, x_60);
x_61 = lean_st_ref_set(x_2, x_52, x_53);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_2, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_64, 5);
x_68 = lean_array_get_size(x_67);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = 0;
x_71 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_49, x_69, x_70, x_67);
lean_dec(x_49);
lean_ctor_set(x_64, 5, x_71);
x_72 = lean_st_ref_set(x_2, x_64, x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_7 = x_73;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
x_77 = lean_ctor_get(x_64, 2);
x_78 = lean_ctor_get(x_64, 3);
x_79 = lean_ctor_get(x_64, 4);
x_80 = lean_ctor_get(x_64, 5);
x_81 = lean_ctor_get(x_64, 6);
x_82 = lean_ctor_get(x_64, 7);
x_83 = lean_ctor_get(x_64, 8);
x_84 = lean_ctor_get(x_64, 9);
x_85 = lean_ctor_get(x_64, 10);
x_86 = lean_ctor_get(x_64, 11);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_87 = lean_array_get_size(x_80);
x_88 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_89 = 0;
x_90 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_49, x_88, x_89, x_80);
lean_dec(x_49);
x_91 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set(x_91, 1, x_76);
lean_ctor_set(x_91, 2, x_77);
lean_ctor_set(x_91, 3, x_78);
lean_ctor_set(x_91, 4, x_79);
lean_ctor_set(x_91, 5, x_90);
lean_ctor_set(x_91, 6, x_81);
lean_ctor_set(x_91, 7, x_82);
lean_ctor_set(x_91, 8, x_83);
lean_ctor_set(x_91, 9, x_84);
lean_ctor_set(x_91, 10, x_85);
lean_ctor_set(x_91, 11, x_86);
x_92 = lean_st_ref_set(x_2, x_91, x_65);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_7 = x_93;
goto _start;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_95 = lean_ctor_get(x_52, 0);
x_96 = lean_ctor_get(x_52, 1);
x_97 = lean_ctor_get(x_52, 2);
x_98 = lean_ctor_get(x_52, 3);
x_99 = lean_ctor_get(x_52, 4);
x_100 = lean_ctor_get(x_52, 5);
x_101 = lean_ctor_get(x_52, 6);
x_102 = lean_ctor_get(x_52, 7);
x_103 = lean_ctor_get(x_52, 8);
x_104 = lean_ctor_get(x_52, 9);
x_105 = lean_ctor_get(x_52, 10);
x_106 = lean_ctor_get(x_52, 11);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_52);
x_107 = lean_unsigned_to_nat(0u);
x_108 = 0;
x_109 = 0;
lean_inc(x_49);
lean_inc(x_19);
if (lean_is_scalar(x_40)) {
 x_110 = lean_alloc_ctor(1, 5, 2);
} else {
 x_110 = x_40;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_19);
lean_ctor_set(x_110, 2, x_37);
lean_ctor_set(x_110, 3, x_46);
lean_ctor_set(x_110, 4, x_49);
lean_ctor_set_uint8(x_110, sizeof(void*)*5, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*5 + 1, x_109);
x_111 = lean_array_push(x_102, x_110);
x_112 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_112, 0, x_95);
lean_ctor_set(x_112, 1, x_96);
lean_ctor_set(x_112, 2, x_97);
lean_ctor_set(x_112, 3, x_98);
lean_ctor_set(x_112, 4, x_99);
lean_ctor_set(x_112, 5, x_100);
lean_ctor_set(x_112, 6, x_101);
lean_ctor_set(x_112, 7, x_111);
lean_ctor_set(x_112, 8, x_103);
lean_ctor_set(x_112, 9, x_104);
lean_ctor_set(x_112, 10, x_105);
lean_ctor_set(x_112, 11, x_106);
x_113 = lean_st_ref_set(x_2, x_112, x_53);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_take(x_2, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 6);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 7);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 8);
lean_inc(x_126);
x_127 = lean_ctor_get(x_116, 9);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 10);
lean_inc(x_128);
x_129 = lean_ctor_get(x_116, 11);
lean_inc(x_129);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 lean_ctor_release(x_116, 6);
 lean_ctor_release(x_116, 7);
 lean_ctor_release(x_116, 8);
 lean_ctor_release(x_116, 9);
 lean_ctor_release(x_116, 10);
 lean_ctor_release(x_116, 11);
 x_130 = x_116;
} else {
 lean_dec_ref(x_116);
 x_130 = lean_box(0);
}
x_131 = lean_array_get_size(x_123);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = 0;
x_134 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_49, x_132, x_133, x_123);
lean_dec(x_49);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 12, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_118);
lean_ctor_set(x_135, 1, x_119);
lean_ctor_set(x_135, 2, x_120);
lean_ctor_set(x_135, 3, x_121);
lean_ctor_set(x_135, 4, x_122);
lean_ctor_set(x_135, 5, x_134);
lean_ctor_set(x_135, 6, x_124);
lean_ctor_set(x_135, 7, x_125);
lean_ctor_set(x_135, 8, x_126);
lean_ctor_set(x_135, 9, x_127);
lean_ctor_set(x_135, 10, x_128);
lean_ctor_set(x_135, 11, x_129);
x_136 = lean_st_ref_set(x_2, x_135, x_117);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_7 = x_137;
goto _start;
}
}
else
{
uint8_t x_139; 
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_48);
if (x_139 == 0)
{
return x_48;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_48, 0);
x_141 = lean_ctor_get(x_48, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_48);
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
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_45);
if (x_143 == 0)
{
return x_45;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_45, 0);
x_145 = lean_ctor_get(x_45, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_45);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; lean_object* x_148; 
lean_dec(x_40);
lean_dec(x_39);
x_147 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_148 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_37, x_38, x_147, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_Expr_fvar___override(x_18);
x_151 = l_Lean_Meta_Closure_pushFVarArg(x_150, x_1, x_2, x_3, x_4, x_5, x_6, x_149);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_7 = x_152;
goto _start;
}
else
{
uint8_t x_154; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_148);
if (x_154 == 0)
{
return x_148;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_148, 0);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_148);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_20);
if (x_162 == 0)
{
return x_20;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_20, 0);
x_164 = lean_ctor_get(x_20, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_20);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
x_11 = lean_nat_dec_lt(x_10, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_instInhabitedLocalDecl;
x_13 = l___private_Init_Util_0__outOfBounds___rarg(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 3);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
lean_dec(x_13);
x_17 = lean_expr_abstract_range(x_15, x_10, x_4);
lean_dec(x_15);
if (x_1 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Expr_forallE___override(x_14, x_17, x_6, x_16);
x_5 = x_10;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Expr_lam___override(x_14, x_17, x_6, x_16);
x_5 = x_10;
x_6 = x_20;
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
x_26 = lean_expr_has_loose_bvar(x_6, x_7);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_27 = lean_expr_lower_loose_bvars(x_6, x_9, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_expr_abstract_range(x_23, x_10, x_4);
lean_dec(x_23);
x_30 = lean_expr_abstract_range(x_24, x_10, x_4);
lean_dec(x_24);
x_31 = l_Lean_Expr_letE___override(x_22, x_29, x_30, x_6, x_25);
x_5 = x_10;
x_6 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_2, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
lean_dec(x_33);
x_37 = lean_expr_abstract_range(x_35, x_10, x_4);
lean_dec(x_35);
if (x_1 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Expr_forallE___override(x_34, x_37, x_6, x_36);
x_5 = x_10;
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Expr_lam___override(x_34, x_37, x_6, x_36);
x_5 = x_10;
x_6 = x_40;
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
x_46 = lean_expr_has_loose_bvar(x_6, x_7);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_47 = lean_expr_lower_loose_bvars(x_6, x_9, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_expr_abstract_range(x_43, x_10, x_4);
lean_dec(x_43);
x_50 = lean_expr_abstract_range(x_44, x_10, x_4);
lean_dec(x_44);
x_51 = l_Lean_Expr_letE___override(x_42, x_49, x_50, x_6, x_45);
x_5 = x_10;
x_6 = x_51;
goto _start;
}
}
}
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
x_6 = 0;
lean_inc(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_5, x_6, x_2);
x_8 = lean_expr_abstract(x_3, x_7);
lean_dec(x_3);
lean_inc(x_4);
x_9 = l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(x_1, x_2, x_4, x_7, x_4, x_8);
lean_dec(x_7);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_instInhabitedLocalDecl;
x_12 = l___private_Init_Util_0__outOfBounds___rarg(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
lean_dec(x_12);
x_16 = lean_expr_abstract_range(x_14, x_9, x_3);
lean_dec(x_14);
x_17 = l_Lean_Expr_lam___override(x_13, x_16, x_5, x_15);
x_4 = x_9;
x_5 = x_17;
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
x_23 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_expr_abstract_range(x_20, x_9, x_3);
lean_dec(x_20);
x_27 = lean_expr_abstract_range(x_21, x_9, x_3);
lean_dec(x_21);
x_28 = l_Lean_Expr_letE___override(x_19, x_26, x_27, x_5, x_22);
x_4 = x_9;
x_5 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_array_fget(x_1, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 3);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_30, sizeof(void*)*4);
lean_dec(x_30);
x_34 = lean_expr_abstract_range(x_32, x_9, x_3);
lean_dec(x_32);
x_35 = l_Lean_Expr_lam___override(x_31, x_34, x_5, x_33);
x_4 = x_9;
x_5 = x_35;
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
x_41 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_42 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_expr_abstract_range(x_38, x_9, x_3);
lean_dec(x_38);
x_45 = lean_expr_abstract_range(x_39, x_9, x_3);
lean_dec(x_39);
x_46 = l_Lean_Expr_letE___override(x_37, x_44, x_45, x_5, x_40);
x_4 = x_9;
x_5 = x_46;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_1);
x_7 = lean_expr_abstract(x_2, x_6);
lean_dec(x_2);
lean_inc(x_3);
x_8 = l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_3, x_6, x_3, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_instInhabitedLocalDecl;
x_12 = l___private_Init_Util_0__outOfBounds___rarg(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
lean_dec(x_12);
x_16 = lean_expr_abstract_range(x_14, x_9, x_3);
lean_dec(x_14);
x_17 = l_Lean_Expr_forallE___override(x_13, x_16, x_5, x_15);
x_4 = x_9;
x_5 = x_17;
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
x_23 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_expr_abstract_range(x_20, x_9, x_3);
lean_dec(x_20);
x_27 = lean_expr_abstract_range(x_21, x_9, x_3);
lean_dec(x_21);
x_28 = l_Lean_Expr_letE___override(x_19, x_26, x_27, x_5, x_22);
x_4 = x_9;
x_5 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_array_fget(x_1, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 3);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_30, sizeof(void*)*4);
lean_dec(x_30);
x_34 = lean_expr_abstract_range(x_32, x_9, x_3);
lean_dec(x_32);
x_35 = l_Lean_Expr_forallE___override(x_31, x_34, x_5, x_33);
x_4 = x_9;
x_5 = x_35;
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
x_41 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_42 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_expr_abstract_range(x_38, x_9, x_3);
lean_dec(x_38);
x_45 = lean_expr_abstract_range(x_39, x_9, x_3);
lean_dec(x_39);
x_46 = l_Lean_Expr_letE___override(x_37, x_44, x_45, x_5, x_40);
x_4 = x_9;
x_5 = x_46;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_1);
x_7 = lean_expr_abstract(x_2, x_6);
lean_dec(x_2);
lean_inc(x_3);
x_8 = l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_3, x_6, x_3, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Meta_resetZetaFVarIds___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
lean_ctor_set_uint8(x_11, 7, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
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
x_49 = lean_ctor_get_uint8(x_11, 8);
x_50 = lean_ctor_get_uint8(x_11, 9);
x_51 = lean_ctor_get_uint8(x_11, 10);
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
lean_ctor_set_uint8(x_55, 7, x_54);
lean_ctor_set_uint8(x_55, 8, x_49);
lean_ctor_set_uint8(x_55, 9, x_50);
lean_ctor_set_uint8(x_55, 10, x_51);
lean_ctor_set_uint8(x_55, 11, x_52);
lean_ctor_set_uint8(x_55, 12, x_53);
lean_ctor_set(x_5, 0, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
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
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_60);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
lean_dec(x_57);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_77 = x_56;
} else {
 lean_dec_ref(x_56);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_79 = lean_ctor_get(x_5, 1);
x_80 = lean_ctor_get(x_5, 2);
x_81 = lean_ctor_get(x_5, 3);
x_82 = lean_ctor_get(x_5, 4);
x_83 = lean_ctor_get(x_5, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_5);
x_84 = lean_ctor_get_uint8(x_11, 0);
x_85 = lean_ctor_get_uint8(x_11, 1);
x_86 = lean_ctor_get_uint8(x_11, 2);
x_87 = lean_ctor_get_uint8(x_11, 3);
x_88 = lean_ctor_get_uint8(x_11, 4);
x_89 = lean_ctor_get_uint8(x_11, 5);
x_90 = lean_ctor_get_uint8(x_11, 6);
x_91 = lean_ctor_get_uint8(x_11, 8);
x_92 = lean_ctor_get_uint8(x_11, 9);
x_93 = lean_ctor_get_uint8(x_11, 10);
x_94 = lean_ctor_get_uint8(x_11, 11);
x_95 = lean_ctor_get_uint8(x_11, 12);
if (lean_is_exclusive(x_11)) {
 x_96 = x_11;
} else {
 lean_dec_ref(x_11);
 x_96 = lean_box(0);
}
x_97 = 1;
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 0, 13);
} else {
 x_98 = x_96;
}
lean_ctor_set_uint8(x_98, 0, x_84);
lean_ctor_set_uint8(x_98, 1, x_85);
lean_ctor_set_uint8(x_98, 2, x_86);
lean_ctor_set_uint8(x_98, 3, x_87);
lean_ctor_set_uint8(x_98, 4, x_88);
lean_ctor_set_uint8(x_98, 5, x_89);
lean_ctor_set_uint8(x_98, 6, x_90);
lean_ctor_set_uint8(x_98, 7, x_97);
lean_ctor_set_uint8(x_98, 8, x_91);
lean_ctor_set_uint8(x_98, 9, x_92);
lean_ctor_set_uint8(x_98, 10, x_93);
lean_ctor_set_uint8(x_98, 11, x_94);
lean_ctor_set_uint8(x_98, 12, x_95);
x_99 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_79);
lean_ctor_set(x_99, 2, x_80);
lean_ctor_set(x_99, 3, x_81);
lean_ctor_set(x_99, 4, x_82);
lean_ctor_set(x_99, 5, x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_99);
x_100 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_99, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_99);
x_103 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_99, x_6, x_7, x_8, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_Closure_process(x_3, x_4, x_99, x_6, x_7, x_8, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_101);
lean_ctor_set(x_109, 1, x_104);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_104);
lean_dec(x_101);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_113 = x_106;
} else {
 lean_dec_ref(x_106);
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
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = lean_ctor_get(x_103, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_117 = x_103;
} else {
 lean_dec_ref(x_103);
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
lean_dec(x_99);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_119 = lean_ctor_get(x_100, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_100, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_121 = x_100;
} else {
 lean_dec_ref(x_100);
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
x_1 = l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
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
x_25 = lean_ctor_get(x_18, 7);
lean_inc(x_25);
x_26 = l_Array_reverse___rarg(x_25);
lean_inc(x_26);
x_27 = l_Lean_Meta_Closure_mkForall(x_26, x_19);
lean_inc(x_24);
x_28 = l_Lean_Meta_Closure_mkForall(x_24, x_27);
x_29 = l_Lean_Meta_Closure_mkLambda(x_26, x_20);
x_30 = l_Lean_Meta_Closure_mkLambda(x_24, x_29);
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
x_46 = lean_ctor_get(x_38, 7);
lean_inc(x_46);
x_47 = l_Array_reverse___rarg(x_46);
lean_inc(x_47);
x_48 = l_Lean_Meta_Closure_mkForall(x_47, x_40);
lean_inc(x_45);
x_49 = l_Lean_Meta_Closure_mkForall(x_45, x_48);
x_50 = l_Lean_Meta_Closure_mkLambda(x_47, x_41);
x_51 = l_Lean_Meta_Closure_mkLambda(x_45, x_50);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_array_to_list(lean_box(0), x_9);
x_11 = l_Lean_Expr_const___override(x_2, x_10);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkAppN(x_11, x_12);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
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
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_array_to_list(lean_box(0), x_18);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_20);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_12, 2);
lean_inc(x_22);
lean_inc(x_22);
lean_inc(x_17);
x_23 = l_Lean_getMaxHeight(x_17, x_22);
x_24 = lean_unbox_uint32(x_23);
lean_dec(x_23);
x_25 = 1;
x_26 = lean_uint32_add(x_24, x_25);
x_27 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_27, 0, x_26);
lean_inc(x_17);
x_28 = l_Lean_Environment_hasUnsafe(x_17, x_20);
x_29 = lean_box(0);
lean_inc(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
if (x_28 == 0)
{
uint8_t x_73; 
lean_inc(x_22);
x_73 = l_Lean_Environment_hasUnsafe(x_17, x_22);
x_31 = x_73;
goto block_72;
}
else
{
uint8_t x_74; 
lean_dec(x_17);
x_74 = 1;
x_31 = x_74;
goto block_72;
}
block_72:
{
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 1;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_34);
x_35 = l_Lean_addDecl(x_34, x_8, x_9, x_16);
if (lean_obj_tag(x_35) == 0)
{
if (x_5 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_37, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_8);
x_40 = l_Lean_compileDecl(x_34, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_41, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
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
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 0;
x_53 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_22);
lean_ctor_set(x_53, 2, x_27);
lean_ctor_set(x_53, 3, x_30);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_54);
x_55 = l_Lean_addDecl(x_54, x_8, x_9, x_16);
if (lean_obj_tag(x_55) == 0)
{
if (x_5 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_57, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_compileDecl(x_54, x_8, x_9, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_61, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_55);
if (x_68 == 0)
{
return x_55;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_55, 0);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_55);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_11);
if (x_75 == 0)
{
return x_11;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_11, 0);
x_77 = lean_ctor_get(x_11, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_11);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
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
l_Lean_Meta_Closure_State_visitedLevel___default = _init_l_Lean_Meta_Closure_State_visitedLevel___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default);
l_Lean_Meta_Closure_State_visitedExpr___default___closed__1 = _init_l_Lean_Meta_Closure_State_visitedExpr___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedExpr___default___closed__1);
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
