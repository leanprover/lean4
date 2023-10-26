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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*);
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
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*);
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
x_6 = lean_hashmap_mk_idx(x_4, x_5);
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
x_8 = lean_hashmap_mk_idx(x_6, x_7);
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
x_17 = lean_hashmap_mk_idx(x_15, x_16);
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
x_9 = lean_hashmap_mk_idx(x_7, x_8);
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
x_25 = lean_hashmap_mk_idx(x_23, x_24);
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
lean_object* x_10; uint8_t x_92; 
x_92 = l_Lean_Level_hasMVar(x_2);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Level_hasParam(x_2);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_94, 1, x_9);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = lean_box(0);
x_10 = x_95;
goto block_91;
}
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_10 = x_96;
goto block_91;
}
block_91:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
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
lean_object* x_10; uint8_t x_92; 
x_92 = l_Lean_Expr_hasLevelParam(x_2);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Expr_hasFVar(x_2);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasMVar(x_2);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_9);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_10 = x_96;
goto block_91;
}
}
else
{
lean_object* x_97; 
x_97 = lean_box(0);
x_10 = x_97;
goto block_91;
}
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_10 = x_98;
goto block_91;
}
block_91:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
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
lean_object* x_23; lean_object* x_24; uint8_t x_54; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_54 = l_Lean_Level_hasMVar(x_23);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Level_hasParam(x_23);
if (x_55 == 0)
{
x_9 = x_23;
x_10 = x_8;
goto block_21;
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
x_24 = x_56;
goto block_53;
}
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_24 = x_57;
goto block_53;
}
block_53:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
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
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_117; uint8_t x_147; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_147 = l_Lean_Level_hasMVar(x_58);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = l_Lean_Level_hasParam(x_58);
if (x_148 == 0)
{
x_60 = x_58;
x_61 = x_8;
goto block_116;
}
else
{
lean_object* x_149; 
x_149 = lean_box(0);
x_117 = x_149;
goto block_146;
}
}
else
{
lean_object* x_150; 
x_150 = lean_box(0);
x_117 = x_150;
goto block_146;
}
block_116:
{
lean_object* x_62; lean_object* x_63; lean_object* x_82; uint8_t x_112; 
x_112 = l_Lean_Level_hasMVar(x_59);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Level_hasParam(x_59);
if (x_113 == 0)
{
x_62 = x_59;
x_63 = x_61;
goto block_81;
}
else
{
lean_object* x_114; 
x_114 = lean_box(0);
x_82 = x_114;
goto block_111;
}
}
else
{
lean_object* x_115; 
x_115 = lean_box(0);
x_82 = x_115;
goto block_111;
}
block_81:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_67 = lean_ptr_addr(x_60);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
lean_dec(x_1);
x_69 = l_Lean_mkLevelMax_x27(x_60, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
else
{
size_t x_71; size_t x_72; uint8_t x_73; 
x_71 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_72 = lean_ptr_addr(x_62);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_74 = l_Lean_mkLevelMax_x27(x_60, x_62);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_63);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_simpLevelMax_x27(x_60, x_62, x_1);
lean_dec(x_1);
lean_dec(x_62);
lean_dec(x_60);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_1);
x_78 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_79 = l_panic___at_Lean_Level_normalize___spec__1(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_63);
return x_80;
}
}
block_111:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
x_83 = lean_st_ref_get(x_3, x_61);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_59);
x_87 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_86, x_59);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_inc(x_59);
x_88 = l_Lean_Meta_Closure_collectLevelAux(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_take(x_3, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_inc(x_89);
x_95 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_94, x_59, x_89);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 7);
lean_inc(x_102);
x_103 = lean_ctor_get(x_92, 8);
lean_inc(x_103);
x_104 = lean_ctor_get(x_92, 9);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 10);
lean_inc(x_105);
x_106 = lean_ctor_get(x_92, 11);
lean_inc(x_106);
lean_dec(x_92);
x_107 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_97);
lean_ctor_set(x_107, 3, x_98);
lean_ctor_set(x_107, 4, x_99);
lean_ctor_set(x_107, 5, x_100);
lean_ctor_set(x_107, 6, x_101);
lean_ctor_set(x_107, 7, x_102);
lean_ctor_set(x_107, 8, x_103);
lean_ctor_set(x_107, 9, x_104);
lean_ctor_set(x_107, 10, x_105);
lean_ctor_set(x_107, 11, x_106);
x_108 = lean_st_ref_set(x_3, x_107, x_93);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_62 = x_89;
x_63 = x_109;
goto block_81;
}
else
{
lean_object* x_110; 
lean_dec(x_59);
x_110 = lean_ctor_get(x_87, 0);
lean_inc(x_110);
lean_dec(x_87);
x_62 = x_110;
x_63 = x_85;
goto block_81;
}
}
}
block_146:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_117);
x_118 = lean_st_ref_get(x_3, x_8);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_58);
x_122 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_121, x_58);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_inc(x_58);
x_123 = l_Lean_Meta_Closure_collectLevelAux(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_120);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_st_ref_take(x_3, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_inc(x_124);
x_130 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_129, x_58, x_124);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 6);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 7);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 8);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 9);
lean_inc(x_139);
x_140 = lean_ctor_get(x_127, 10);
lean_inc(x_140);
x_141 = lean_ctor_get(x_127, 11);
lean_inc(x_141);
lean_dec(x_127);
x_142 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_142, 0, x_130);
lean_ctor_set(x_142, 1, x_131);
lean_ctor_set(x_142, 2, x_132);
lean_ctor_set(x_142, 3, x_133);
lean_ctor_set(x_142, 4, x_134);
lean_ctor_set(x_142, 5, x_135);
lean_ctor_set(x_142, 6, x_136);
lean_ctor_set(x_142, 7, x_137);
lean_ctor_set(x_142, 8, x_138);
lean_ctor_set(x_142, 9, x_139);
lean_ctor_set(x_142, 10, x_140);
lean_ctor_set(x_142, 11, x_141);
x_143 = lean_st_ref_set(x_3, x_142, x_128);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_60 = x_124;
x_61 = x_144;
goto block_116;
}
else
{
lean_object* x_145; 
lean_dec(x_58);
x_145 = lean_ctor_get(x_122, 0);
lean_inc(x_145);
lean_dec(x_122);
x_60 = x_145;
x_61 = x_120;
goto block_116;
}
}
}
case 3:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_210; uint8_t x_240; 
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
x_240 = l_Lean_Level_hasMVar(x_151);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Level_hasParam(x_151);
if (x_241 == 0)
{
x_153 = x_151;
x_154 = x_8;
goto block_209;
}
else
{
lean_object* x_242; 
x_242 = lean_box(0);
x_210 = x_242;
goto block_239;
}
}
else
{
lean_object* x_243; 
x_243 = lean_box(0);
x_210 = x_243;
goto block_239;
}
block_209:
{
lean_object* x_155; lean_object* x_156; lean_object* x_175; uint8_t x_205; 
x_205 = l_Lean_Level_hasMVar(x_152);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = l_Lean_Level_hasParam(x_152);
if (x_206 == 0)
{
x_155 = x_152;
x_156 = x_154;
goto block_174;
}
else
{
lean_object* x_207; 
x_207 = lean_box(0);
x_175 = x_207;
goto block_204;
}
}
else
{
lean_object* x_208; 
x_208 = lean_box(0);
x_175 = x_208;
goto block_204;
}
block_174:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_157; lean_object* x_158; size_t x_159; size_t x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_160 = lean_ptr_addr(x_153);
x_161 = lean_usize_dec_eq(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_158);
lean_dec(x_1);
x_162 = l_Lean_mkLevelIMax_x27(x_153, x_155);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
else
{
size_t x_164; size_t x_165; uint8_t x_166; 
x_164 = lean_ptr_addr(x_158);
lean_dec(x_158);
x_165 = lean_ptr_addr(x_155);
x_166 = lean_usize_dec_eq(x_164, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_1);
x_167 = l_Lean_mkLevelIMax_x27(x_153, x_155);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_156);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Lean_simpLevelIMax_x27(x_153, x_155, x_1);
lean_dec(x_1);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_156);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_1);
x_171 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_172 = l_panic___at_Lean_Level_normalize___spec__1(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_156);
return x_173;
}
}
block_204:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_175);
x_176 = lean_st_ref_get(x_3, x_154);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_152);
x_180 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_179, x_152);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_inc(x_152);
x_181 = l_Lean_Meta_Closure_collectLevelAux(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_178);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_st_ref_take(x_3, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_inc(x_182);
x_188 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_187, x_152, x_182);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_185, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_185, 5);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 6);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 7);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 8);
lean_inc(x_196);
x_197 = lean_ctor_get(x_185, 9);
lean_inc(x_197);
x_198 = lean_ctor_get(x_185, 10);
lean_inc(x_198);
x_199 = lean_ctor_get(x_185, 11);
lean_inc(x_199);
lean_dec(x_185);
x_200 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_200, 0, x_188);
lean_ctor_set(x_200, 1, x_189);
lean_ctor_set(x_200, 2, x_190);
lean_ctor_set(x_200, 3, x_191);
lean_ctor_set(x_200, 4, x_192);
lean_ctor_set(x_200, 5, x_193);
lean_ctor_set(x_200, 6, x_194);
lean_ctor_set(x_200, 7, x_195);
lean_ctor_set(x_200, 8, x_196);
lean_ctor_set(x_200, 9, x_197);
lean_ctor_set(x_200, 10, x_198);
lean_ctor_set(x_200, 11, x_199);
x_201 = lean_st_ref_set(x_3, x_200, x_186);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_155 = x_182;
x_156 = x_202;
goto block_174;
}
else
{
lean_object* x_203; 
lean_dec(x_152);
x_203 = lean_ctor_get(x_180, 0);
lean_inc(x_203);
lean_dec(x_180);
x_155 = x_203;
x_156 = x_178;
goto block_174;
}
}
}
block_239:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_210);
x_211 = lean_st_ref_get(x_3, x_8);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_151);
x_215 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_214, x_151);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_inc(x_151);
x_216 = l_Lean_Meta_Closure_collectLevelAux(x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_213);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_st_ref_take(x_3, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_inc(x_217);
x_223 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_222, x_151, x_217);
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 4);
lean_inc(x_227);
x_228 = lean_ctor_get(x_220, 5);
lean_inc(x_228);
x_229 = lean_ctor_get(x_220, 6);
lean_inc(x_229);
x_230 = lean_ctor_get(x_220, 7);
lean_inc(x_230);
x_231 = lean_ctor_get(x_220, 8);
lean_inc(x_231);
x_232 = lean_ctor_get(x_220, 9);
lean_inc(x_232);
x_233 = lean_ctor_get(x_220, 10);
lean_inc(x_233);
x_234 = lean_ctor_get(x_220, 11);
lean_inc(x_234);
lean_dec(x_220);
x_235 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_235, 0, x_223);
lean_ctor_set(x_235, 1, x_224);
lean_ctor_set(x_235, 2, x_225);
lean_ctor_set(x_235, 3, x_226);
lean_ctor_set(x_235, 4, x_227);
lean_ctor_set(x_235, 5, x_228);
lean_ctor_set(x_235, 6, x_229);
lean_ctor_set(x_235, 7, x_230);
lean_ctor_set(x_235, 8, x_231);
lean_ctor_set(x_235, 9, x_232);
lean_ctor_set(x_235, 10, x_233);
lean_ctor_set(x_235, 11, x_234);
x_236 = lean_st_ref_set(x_3, x_235, x_221);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_153 = x_217;
x_154 = x_237;
goto block_209;
}
else
{
lean_object* x_238; 
lean_dec(x_151);
x_238 = lean_ctor_get(x_215, 0);
lean_inc(x_238);
lean_dec(x_215);
x_153 = x_238;
x_154 = x_213;
goto block_209;
}
}
}
default: 
{
lean_object* x_244; 
x_244 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_244;
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
lean_object* x_9; uint8_t x_81; 
x_81 = l_Lean_Level_hasMVar(x_1);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Level_hasParam(x_1);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_8);
return x_83;
}
else
{
lean_object* x_84; 
x_84 = lean_box(0);
x_9 = x_84;
goto block_80;
}
}
else
{
lean_object* x_85; 
x_85 = lean_box(0);
x_9 = x_85;
goto block_80;
}
block_80:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_9);
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
x_3 = lean_unsigned_to_nat(1509u);
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
x_3 = lean_unsigned_to_nat(1520u);
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
x_3 = lean_unsigned_to_nat(1471u);
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
x_3 = lean_unsigned_to_nat(1566u);
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
x_3 = lean_unsigned_to_nat(1546u);
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
x_3 = lean_unsigned_to_nat(1575u);
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
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_143; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_143 = l_Lean_Expr_hasLevelParam(x_69);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = l_Lean_Expr_hasFVar(x_69);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Expr_hasMVar(x_69);
if (x_145 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_67;
}
else
{
lean_object* x_146; 
lean_free_object(x_67);
x_146 = lean_box(0);
x_71 = x_146;
goto block_142;
}
}
else
{
lean_object* x_147; 
lean_free_object(x_67);
x_147 = lean_box(0);
x_71 = x_147;
goto block_142;
}
}
else
{
lean_object* x_148; 
lean_free_object(x_67);
x_148 = lean_box(0);
x_71 = x_148;
goto block_142;
}
block_142:
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_71);
x_72 = lean_st_ref_get(x_3, x_70);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_69);
x_77 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_76, x_69);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_free_object(x_72);
lean_inc(x_69);
x_78 = l_Lean_Meta_Closure_collectExprAux(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
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
x_86 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_85, x_69, x_79);
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
lean_dec(x_69);
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
lean_dec(x_69);
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
lean_inc(x_69);
x_111 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_110, x_69);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_inc(x_69);
x_112 = l_Lean_Meta_Closure_collectExprAux(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_109);
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
x_120 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_119, x_69, x_113);
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
lean_dec(x_69);
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
lean_dec(x_69);
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
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_189; 
x_149 = lean_ctor_get(x_67, 0);
x_150 = lean_ctor_get(x_67, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_67);
x_189 = l_Lean_Expr_hasLevelParam(x_149);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = l_Lean_Expr_hasFVar(x_149);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = l_Lean_Expr_hasMVar(x_149);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_149);
lean_ctor_set(x_192, 1, x_150);
return x_192;
}
else
{
lean_object* x_193; 
x_193 = lean_box(0);
x_151 = x_193;
goto block_188;
}
}
else
{
lean_object* x_194; 
x_194 = lean_box(0);
x_151 = x_194;
goto block_188;
}
}
else
{
lean_object* x_195; 
x_195 = lean_box(0);
x_151 = x_195;
goto block_188;
}
block_188:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_151);
x_152 = lean_st_ref_get(x_3, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
lean_inc(x_149);
x_157 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_156, x_149);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
lean_dec(x_155);
lean_inc(x_149);
x_158 = l_Lean_Meta_Closure_collectExprAux(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_154);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_take(x_3, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_inc(x_159);
x_166 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_165, x_149, x_159);
x_167 = lean_ctor_get(x_162, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 5);
lean_inc(x_170);
x_171 = lean_ctor_get(x_162, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_162, 7);
lean_inc(x_172);
x_173 = lean_ctor_get(x_162, 8);
lean_inc(x_173);
x_174 = lean_ctor_get(x_162, 9);
lean_inc(x_174);
x_175 = lean_ctor_get(x_162, 10);
lean_inc(x_175);
x_176 = lean_ctor_get(x_162, 11);
lean_inc(x_176);
lean_dec(x_162);
x_177 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_177, 0, x_164);
lean_ctor_set(x_177, 1, x_166);
lean_ctor_set(x_177, 2, x_167);
lean_ctor_set(x_177, 3, x_168);
lean_ctor_set(x_177, 4, x_169);
lean_ctor_set(x_177, 5, x_170);
lean_ctor_set(x_177, 6, x_171);
lean_ctor_set(x_177, 7, x_172);
lean_ctor_set(x_177, 8, x_173);
lean_ctor_set(x_177, 9, x_174);
lean_ctor_set(x_177, 10, x_175);
lean_ctor_set(x_177, 11, x_176);
x_178 = lean_st_ref_set(x_3, x_177, x_163);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_159);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_149);
x_182 = lean_ctor_get(x_158, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_158, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_184 = x_158;
} else {
 lean_dec_ref(x_158);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_149);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_186 = lean_ctor_get(x_157, 0);
lean_inc(x_186);
lean_dec(x_157);
if (lean_is_scalar(x_155)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_155;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_154);
return x_187;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_196 = !lean_is_exclusive(x_67);
if (x_196 == 0)
{
return x_67;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_67, 0);
x_198 = lean_ctor_get(x_67, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_67);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_39);
if (x_200 == 0)
{
return x_39;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_39, 0);
x_202 = lean_ctor_get(x_39, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_39);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
case 2:
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_1, 0);
lean_inc(x_204);
x_205 = l_Lean_MVarId_getDecl(x_204, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 2);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_209 = l_Lean_Meta_Closure_preprocess(x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_250; uint8_t x_284; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_284 = l_Lean_Expr_hasLevelParam(x_210);
if (x_284 == 0)
{
uint8_t x_285; 
x_285 = l_Lean_Expr_hasFVar(x_210);
if (x_285 == 0)
{
uint8_t x_286; 
x_286 = l_Lean_Expr_hasMVar(x_210);
if (x_286 == 0)
{
x_212 = x_210;
x_213 = x_211;
goto block_249;
}
else
{
lean_object* x_287; 
x_287 = lean_box(0);
x_250 = x_287;
goto block_283;
}
}
else
{
lean_object* x_288; 
x_288 = lean_box(0);
x_250 = x_288;
goto block_283;
}
}
else
{
lean_object* x_289; 
x_289 = lean_box(0);
x_250 = x_289;
goto block_283;
}
block_249:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_214 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_216);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_st_ref_take(x_3, x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_221, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_221, 4);
lean_inc(x_227);
x_228 = lean_ctor_get(x_221, 5);
lean_inc(x_228);
x_229 = lean_ctor_get(x_221, 6);
lean_inc(x_229);
x_230 = lean_unsigned_to_nat(0u);
x_231 = 0;
x_232 = 0;
lean_inc(x_215);
x_233 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_215);
lean_ctor_set(x_233, 2, x_218);
lean_ctor_set(x_233, 3, x_212);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 1, x_232);
x_234 = lean_array_push(x_229, x_233);
x_235 = lean_ctor_get(x_221, 7);
lean_inc(x_235);
x_236 = lean_ctor_get(x_221, 8);
lean_inc(x_236);
x_237 = lean_ctor_get(x_221, 9);
lean_inc(x_237);
x_238 = lean_array_push(x_237, x_1);
x_239 = lean_ctor_get(x_221, 10);
lean_inc(x_239);
x_240 = lean_ctor_get(x_221, 11);
lean_inc(x_240);
lean_dec(x_221);
x_241 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_241, 0, x_223);
lean_ctor_set(x_241, 1, x_224);
lean_ctor_set(x_241, 2, x_225);
lean_ctor_set(x_241, 3, x_226);
lean_ctor_set(x_241, 4, x_227);
lean_ctor_set(x_241, 5, x_228);
lean_ctor_set(x_241, 6, x_234);
lean_ctor_set(x_241, 7, x_235);
lean_ctor_set(x_241, 8, x_236);
lean_ctor_set(x_241, 9, x_238);
lean_ctor_set(x_241, 10, x_239);
lean_ctor_set(x_241, 11, x_240);
x_242 = lean_st_ref_set(x_3, x_241, x_222);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_242, 0);
lean_dec(x_244);
x_245 = l_Lean_Expr_fvar___override(x_215);
lean_ctor_set(x_242, 0, x_245);
return x_242;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
x_247 = l_Lean_Expr_fvar___override(x_215);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
block_283:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_250);
x_251 = lean_st_ref_get(x_3, x_211);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_210);
x_255 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_254, x_210);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_210);
x_256 = l_Lean_Meta_Closure_collectExprAux(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_st_ref_take(x_3, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_inc(x_257);
x_264 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_263, x_210, x_257);
x_265 = lean_ctor_get(x_260, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_260, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_260, 4);
lean_inc(x_267);
x_268 = lean_ctor_get(x_260, 5);
lean_inc(x_268);
x_269 = lean_ctor_get(x_260, 6);
lean_inc(x_269);
x_270 = lean_ctor_get(x_260, 7);
lean_inc(x_270);
x_271 = lean_ctor_get(x_260, 8);
lean_inc(x_271);
x_272 = lean_ctor_get(x_260, 9);
lean_inc(x_272);
x_273 = lean_ctor_get(x_260, 10);
lean_inc(x_273);
x_274 = lean_ctor_get(x_260, 11);
lean_inc(x_274);
lean_dec(x_260);
x_275 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_275, 0, x_262);
lean_ctor_set(x_275, 1, x_264);
lean_ctor_set(x_275, 2, x_265);
lean_ctor_set(x_275, 3, x_266);
lean_ctor_set(x_275, 4, x_267);
lean_ctor_set(x_275, 5, x_268);
lean_ctor_set(x_275, 6, x_269);
lean_ctor_set(x_275, 7, x_270);
lean_ctor_set(x_275, 8, x_271);
lean_ctor_set(x_275, 9, x_272);
lean_ctor_set(x_275, 10, x_273);
lean_ctor_set(x_275, 11, x_274);
x_276 = lean_st_ref_set(x_3, x_275, x_261);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_212 = x_257;
x_213 = x_277;
goto block_249;
}
else
{
uint8_t x_278; 
lean_dec(x_210);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_256);
if (x_278 == 0)
{
return x_256;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_256, 0);
x_280 = lean_ctor_get(x_256, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_256);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
lean_object* x_282; 
lean_dec(x_210);
x_282 = lean_ctor_get(x_255, 0);
lean_inc(x_282);
lean_dec(x_255);
x_212 = x_282;
x_213 = x_253;
goto block_249;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_209);
if (x_290 == 0)
{
return x_209;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_209, 0);
x_292 = lean_ctor_get(x_209, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_209);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_205);
if (x_294 == 0)
{
return x_205;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_205, 0);
x_296 = lean_ctor_get(x_205, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_205);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
case 3:
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_1, 0);
lean_inc(x_298);
lean_inc(x_298);
x_299 = l_Lean_Meta_Closure_collectLevel(x_298, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; size_t x_302; size_t x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_299, 0);
x_302 = lean_ptr_addr(x_298);
lean_dec(x_298);
x_303 = lean_ptr_addr(x_301);
x_304 = lean_usize_dec_eq(x_302, x_303);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_1);
x_305 = l_Lean_Expr_sort___override(x_301);
lean_ctor_set(x_299, 0, x_305);
return x_299;
}
else
{
lean_dec(x_301);
lean_ctor_set(x_299, 0, x_1);
return x_299;
}
}
else
{
lean_object* x_306; lean_object* x_307; size_t x_308; size_t x_309; uint8_t x_310; 
x_306 = lean_ctor_get(x_299, 0);
x_307 = lean_ctor_get(x_299, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_299);
x_308 = lean_ptr_addr(x_298);
lean_dec(x_298);
x_309 = lean_ptr_addr(x_306);
x_310 = lean_usize_dec_eq(x_308, x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_1);
x_311 = l_Lean_Expr_sort___override(x_306);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_307);
return x_312;
}
else
{
lean_object* x_313; 
lean_dec(x_306);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_1);
lean_ctor_set(x_313, 1, x_307);
return x_313;
}
}
}
case 4:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_314 = lean_ctor_get(x_1, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_1, 1);
lean_inc(x_315);
x_316 = lean_box(0);
lean_inc(x_315);
x_317 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_315, x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = l_ptrEqList___rarg(x_315, x_319);
lean_dec(x_315);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_1);
x_321 = l_Lean_Expr_const___override(x_314, x_319);
lean_ctor_set(x_317, 0, x_321);
return x_317;
}
else
{
lean_dec(x_319);
lean_dec(x_314);
lean_ctor_set(x_317, 0, x_1);
return x_317;
}
}
else
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_317, 0);
x_323 = lean_ctor_get(x_317, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_317);
x_324 = l_ptrEqList___rarg(x_315, x_322);
lean_dec(x_315);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_1);
x_325 = l_Lean_Expr_const___override(x_314, x_322);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_323);
return x_326;
}
else
{
lean_object* x_327; 
lean_dec(x_322);
lean_dec(x_314);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_1);
lean_ctor_set(x_327, 1, x_323);
return x_327;
}
}
}
case 5:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_392; uint8_t x_426; 
x_328 = lean_ctor_get(x_1, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_1, 1);
lean_inc(x_329);
x_426 = l_Lean_Expr_hasLevelParam(x_328);
if (x_426 == 0)
{
uint8_t x_427; 
x_427 = l_Lean_Expr_hasFVar(x_328);
if (x_427 == 0)
{
uint8_t x_428; 
x_428 = l_Lean_Expr_hasMVar(x_328);
if (x_428 == 0)
{
x_330 = x_328;
x_331 = x_8;
goto block_391;
}
else
{
lean_object* x_429; 
x_429 = lean_box(0);
x_392 = x_429;
goto block_425;
}
}
else
{
lean_object* x_430; 
x_430 = lean_box(0);
x_392 = x_430;
goto block_425;
}
}
else
{
lean_object* x_431; 
x_431 = lean_box(0);
x_392 = x_431;
goto block_425;
}
block_391:
{
lean_object* x_332; lean_object* x_333; lean_object* x_351; uint8_t x_385; 
x_385 = l_Lean_Expr_hasLevelParam(x_329);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = l_Lean_Expr_hasFVar(x_329);
if (x_386 == 0)
{
uint8_t x_387; 
x_387 = l_Lean_Expr_hasMVar(x_329);
if (x_387 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_332 = x_329;
x_333 = x_331;
goto block_350;
}
else
{
lean_object* x_388; 
x_388 = lean_box(0);
x_351 = x_388;
goto block_384;
}
}
else
{
lean_object* x_389; 
x_389 = lean_box(0);
x_351 = x_389;
goto block_384;
}
}
else
{
lean_object* x_390; 
x_390 = lean_box(0);
x_351 = x_390;
goto block_384;
}
block_350:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_334; lean_object* x_335; size_t x_336; size_t x_337; uint8_t x_338; 
x_334 = lean_ctor_get(x_1, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_1, 1);
lean_inc(x_335);
x_336 = lean_ptr_addr(x_334);
lean_dec(x_334);
x_337 = lean_ptr_addr(x_330);
x_338 = lean_usize_dec_eq(x_336, x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_335);
lean_dec(x_1);
x_339 = l_Lean_Expr_app___override(x_330, x_332);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_333);
return x_340;
}
else
{
size_t x_341; size_t x_342; uint8_t x_343; 
x_341 = lean_ptr_addr(x_335);
lean_dec(x_335);
x_342 = lean_ptr_addr(x_332);
x_343 = lean_usize_dec_eq(x_341, x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_1);
x_344 = l_Lean_Expr_app___override(x_330, x_332);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_333);
return x_345;
}
else
{
lean_object* x_346; 
lean_dec(x_332);
lean_dec(x_330);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_333);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_1);
x_347 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_348 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_333);
return x_349;
}
}
block_384:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_351);
x_352 = lean_st_ref_get(x_3, x_331);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_inc(x_329);
x_356 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_355, x_329);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; 
lean_inc(x_329);
x_357 = l_Lean_Meta_Closure_collectExprAux(x_329, x_2, x_3, x_4, x_5, x_6, x_7, x_354);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_st_ref_take(x_3, x_359);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_361, 1);
lean_inc(x_364);
lean_inc(x_358);
x_365 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_364, x_329, x_358);
x_366 = lean_ctor_get(x_361, 2);
lean_inc(x_366);
x_367 = lean_ctor_get(x_361, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_361, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_361, 5);
lean_inc(x_369);
x_370 = lean_ctor_get(x_361, 6);
lean_inc(x_370);
x_371 = lean_ctor_get(x_361, 7);
lean_inc(x_371);
x_372 = lean_ctor_get(x_361, 8);
lean_inc(x_372);
x_373 = lean_ctor_get(x_361, 9);
lean_inc(x_373);
x_374 = lean_ctor_get(x_361, 10);
lean_inc(x_374);
x_375 = lean_ctor_get(x_361, 11);
lean_inc(x_375);
lean_dec(x_361);
x_376 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_376, 0, x_363);
lean_ctor_set(x_376, 1, x_365);
lean_ctor_set(x_376, 2, x_366);
lean_ctor_set(x_376, 3, x_367);
lean_ctor_set(x_376, 4, x_368);
lean_ctor_set(x_376, 5, x_369);
lean_ctor_set(x_376, 6, x_370);
lean_ctor_set(x_376, 7, x_371);
lean_ctor_set(x_376, 8, x_372);
lean_ctor_set(x_376, 9, x_373);
lean_ctor_set(x_376, 10, x_374);
lean_ctor_set(x_376, 11, x_375);
x_377 = lean_st_ref_set(x_3, x_376, x_362);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_332 = x_358;
x_333 = x_378;
goto block_350;
}
else
{
uint8_t x_379; 
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_357);
if (x_379 == 0)
{
return x_357;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_357, 0);
x_381 = lean_ctor_get(x_357, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_357);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; 
lean_dec(x_329);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_383 = lean_ctor_get(x_356, 0);
lean_inc(x_383);
lean_dec(x_356);
x_332 = x_383;
x_333 = x_354;
goto block_350;
}
}
}
block_425:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_392);
x_393 = lean_st_ref_get(x_3, x_8);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
lean_inc(x_328);
x_397 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_396, x_328);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_328);
x_398 = l_Lean_Meta_Closure_collectExprAux(x_328, x_2, x_3, x_4, x_5, x_6, x_7, x_395);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_st_ref_take(x_3, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_inc(x_399);
x_406 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_405, x_328, x_399);
x_407 = lean_ctor_get(x_402, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_402, 3);
lean_inc(x_408);
x_409 = lean_ctor_get(x_402, 4);
lean_inc(x_409);
x_410 = lean_ctor_get(x_402, 5);
lean_inc(x_410);
x_411 = lean_ctor_get(x_402, 6);
lean_inc(x_411);
x_412 = lean_ctor_get(x_402, 7);
lean_inc(x_412);
x_413 = lean_ctor_get(x_402, 8);
lean_inc(x_413);
x_414 = lean_ctor_get(x_402, 9);
lean_inc(x_414);
x_415 = lean_ctor_get(x_402, 10);
lean_inc(x_415);
x_416 = lean_ctor_get(x_402, 11);
lean_inc(x_416);
lean_dec(x_402);
x_417 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_417, 0, x_404);
lean_ctor_set(x_417, 1, x_406);
lean_ctor_set(x_417, 2, x_407);
lean_ctor_set(x_417, 3, x_408);
lean_ctor_set(x_417, 4, x_409);
lean_ctor_set(x_417, 5, x_410);
lean_ctor_set(x_417, 6, x_411);
lean_ctor_set(x_417, 7, x_412);
lean_ctor_set(x_417, 8, x_413);
lean_ctor_set(x_417, 9, x_414);
lean_ctor_set(x_417, 10, x_415);
lean_ctor_set(x_417, 11, x_416);
x_418 = lean_st_ref_set(x_3, x_417, x_403);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_330 = x_399;
x_331 = x_419;
goto block_391;
}
else
{
uint8_t x_420; 
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_398);
if (x_420 == 0)
{
return x_398;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_398, 0);
x_422 = lean_ctor_get(x_398, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_398);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
else
{
lean_object* x_424; 
lean_dec(x_328);
x_424 = lean_ctor_get(x_397, 0);
lean_inc(x_424);
lean_dec(x_397);
x_330 = x_424;
x_331 = x_395;
goto block_391;
}
}
}
case 6:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_502; uint8_t x_536; 
x_432 = lean_ctor_get(x_1, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_1, 2);
lean_inc(x_433);
x_536 = l_Lean_Expr_hasLevelParam(x_432);
if (x_536 == 0)
{
uint8_t x_537; 
x_537 = l_Lean_Expr_hasFVar(x_432);
if (x_537 == 0)
{
uint8_t x_538; 
x_538 = l_Lean_Expr_hasMVar(x_432);
if (x_538 == 0)
{
x_434 = x_432;
x_435 = x_8;
goto block_501;
}
else
{
lean_object* x_539; 
x_539 = lean_box(0);
x_502 = x_539;
goto block_535;
}
}
else
{
lean_object* x_540; 
x_540 = lean_box(0);
x_502 = x_540;
goto block_535;
}
}
else
{
lean_object* x_541; 
x_541 = lean_box(0);
x_502 = x_541;
goto block_535;
}
block_501:
{
lean_object* x_436; lean_object* x_437; lean_object* x_461; uint8_t x_495; 
x_495 = l_Lean_Expr_hasLevelParam(x_433);
if (x_495 == 0)
{
uint8_t x_496; 
x_496 = l_Lean_Expr_hasFVar(x_433);
if (x_496 == 0)
{
uint8_t x_497; 
x_497 = l_Lean_Expr_hasMVar(x_433);
if (x_497 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_436 = x_433;
x_437 = x_435;
goto block_460;
}
else
{
lean_object* x_498; 
x_498 = lean_box(0);
x_461 = x_498;
goto block_494;
}
}
else
{
lean_object* x_499; 
x_499 = lean_box(0);
x_461 = x_499;
goto block_494;
}
}
else
{
lean_object* x_500; 
x_500 = lean_box(0);
x_461 = x_500;
goto block_494;
}
block_460:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; size_t x_443; size_t x_444; uint8_t x_445; 
x_438 = lean_ctor_get(x_1, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_1, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_1, 2);
lean_inc(x_440);
x_441 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
x_442 = l_Lean_Expr_lam___override(x_438, x_439, x_440, x_441);
x_443 = lean_ptr_addr(x_439);
lean_dec(x_439);
x_444 = lean_ptr_addr(x_434);
x_445 = lean_usize_dec_eq(x_443, x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_442);
lean_dec(x_440);
x_446 = l_Lean_Expr_lam___override(x_438, x_434, x_436, x_441);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_437);
return x_447;
}
else
{
size_t x_448; size_t x_449; uint8_t x_450; 
x_448 = lean_ptr_addr(x_440);
lean_dec(x_440);
x_449 = lean_ptr_addr(x_436);
x_450 = lean_usize_dec_eq(x_448, x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_442);
x_451 = l_Lean_Expr_lam___override(x_438, x_434, x_436, x_441);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_437);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_441, x_441);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_442);
x_454 = l_Lean_Expr_lam___override(x_438, x_434, x_436, x_441);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_437);
return x_455;
}
else
{
lean_object* x_456; 
lean_dec(x_438);
lean_dec(x_436);
lean_dec(x_434);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_442);
lean_ctor_set(x_456, 1, x_437);
return x_456;
}
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_1);
x_457 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_458 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_457);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_437);
return x_459;
}
}
block_494:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_461);
x_462 = lean_st_ref_get(x_3, x_435);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_433);
x_466 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_465, x_433);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
lean_inc(x_433);
x_467 = l_Lean_Meta_Closure_collectExprAux(x_433, x_2, x_3, x_4, x_5, x_6, x_7, x_464);
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
x_475 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_474, x_433, x_468);
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
x_436 = x_468;
x_437 = x_488;
goto block_460;
}
else
{
uint8_t x_489; 
lean_dec(x_434);
lean_dec(x_433);
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
lean_dec(x_433);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_493 = lean_ctor_get(x_466, 0);
lean_inc(x_493);
lean_dec(x_466);
x_436 = x_493;
x_437 = x_464;
goto block_460;
}
}
}
block_535:
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_502);
x_503 = lean_st_ref_get(x_3, x_8);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
lean_inc(x_432);
x_507 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_506, x_432);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_432);
x_508 = l_Lean_Meta_Closure_collectExprAux(x_432, x_2, x_3, x_4, x_5, x_6, x_7, x_505);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_st_ref_take(x_3, x_510);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_ctor_get(x_512, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_515);
lean_inc(x_509);
x_516 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_515, x_432, x_509);
x_517 = lean_ctor_get(x_512, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_512, 3);
lean_inc(x_518);
x_519 = lean_ctor_get(x_512, 4);
lean_inc(x_519);
x_520 = lean_ctor_get(x_512, 5);
lean_inc(x_520);
x_521 = lean_ctor_get(x_512, 6);
lean_inc(x_521);
x_522 = lean_ctor_get(x_512, 7);
lean_inc(x_522);
x_523 = lean_ctor_get(x_512, 8);
lean_inc(x_523);
x_524 = lean_ctor_get(x_512, 9);
lean_inc(x_524);
x_525 = lean_ctor_get(x_512, 10);
lean_inc(x_525);
x_526 = lean_ctor_get(x_512, 11);
lean_inc(x_526);
lean_dec(x_512);
x_527 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_527, 0, x_514);
lean_ctor_set(x_527, 1, x_516);
lean_ctor_set(x_527, 2, x_517);
lean_ctor_set(x_527, 3, x_518);
lean_ctor_set(x_527, 4, x_519);
lean_ctor_set(x_527, 5, x_520);
lean_ctor_set(x_527, 6, x_521);
lean_ctor_set(x_527, 7, x_522);
lean_ctor_set(x_527, 8, x_523);
lean_ctor_set(x_527, 9, x_524);
lean_ctor_set(x_527, 10, x_525);
lean_ctor_set(x_527, 11, x_526);
x_528 = lean_st_ref_set(x_3, x_527, x_513);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
lean_dec(x_528);
x_434 = x_509;
x_435 = x_529;
goto block_501;
}
else
{
uint8_t x_530; 
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_530 = !lean_is_exclusive(x_508);
if (x_530 == 0)
{
return x_508;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_508, 0);
x_532 = lean_ctor_get(x_508, 1);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_508);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
}
else
{
lean_object* x_534; 
lean_dec(x_432);
x_534 = lean_ctor_get(x_507, 0);
lean_inc(x_534);
lean_dec(x_507);
x_434 = x_534;
x_435 = x_505;
goto block_501;
}
}
}
case 7:
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_612; uint8_t x_646; 
x_542 = lean_ctor_get(x_1, 1);
lean_inc(x_542);
x_543 = lean_ctor_get(x_1, 2);
lean_inc(x_543);
x_646 = l_Lean_Expr_hasLevelParam(x_542);
if (x_646 == 0)
{
uint8_t x_647; 
x_647 = l_Lean_Expr_hasFVar(x_542);
if (x_647 == 0)
{
uint8_t x_648; 
x_648 = l_Lean_Expr_hasMVar(x_542);
if (x_648 == 0)
{
x_544 = x_542;
x_545 = x_8;
goto block_611;
}
else
{
lean_object* x_649; 
x_649 = lean_box(0);
x_612 = x_649;
goto block_645;
}
}
else
{
lean_object* x_650; 
x_650 = lean_box(0);
x_612 = x_650;
goto block_645;
}
}
else
{
lean_object* x_651; 
x_651 = lean_box(0);
x_612 = x_651;
goto block_645;
}
block_611:
{
lean_object* x_546; lean_object* x_547; lean_object* x_571; uint8_t x_605; 
x_605 = l_Lean_Expr_hasLevelParam(x_543);
if (x_605 == 0)
{
uint8_t x_606; 
x_606 = l_Lean_Expr_hasFVar(x_543);
if (x_606 == 0)
{
uint8_t x_607; 
x_607 = l_Lean_Expr_hasMVar(x_543);
if (x_607 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_546 = x_543;
x_547 = x_545;
goto block_570;
}
else
{
lean_object* x_608; 
x_608 = lean_box(0);
x_571 = x_608;
goto block_604;
}
}
else
{
lean_object* x_609; 
x_609 = lean_box(0);
x_571 = x_609;
goto block_604;
}
}
else
{
lean_object* x_610; 
x_610 = lean_box(0);
x_571 = x_610;
goto block_604;
}
block_570:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; size_t x_553; size_t x_554; uint8_t x_555; 
x_548 = lean_ctor_get(x_1, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_1, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_1, 2);
lean_inc(x_550);
x_551 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_550);
lean_inc(x_549);
lean_inc(x_548);
x_552 = l_Lean_Expr_forallE___override(x_548, x_549, x_550, x_551);
x_553 = lean_ptr_addr(x_549);
lean_dec(x_549);
x_554 = lean_ptr_addr(x_544);
x_555 = lean_usize_dec_eq(x_553, x_554);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; 
lean_dec(x_552);
lean_dec(x_550);
x_556 = l_Lean_Expr_forallE___override(x_548, x_544, x_546, x_551);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_547);
return x_557;
}
else
{
size_t x_558; size_t x_559; uint8_t x_560; 
x_558 = lean_ptr_addr(x_550);
lean_dec(x_550);
x_559 = lean_ptr_addr(x_546);
x_560 = lean_usize_dec_eq(x_558, x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_552);
x_561 = l_Lean_Expr_forallE___override(x_548, x_544, x_546, x_551);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_547);
return x_562;
}
else
{
uint8_t x_563; 
x_563 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_551, x_551);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; 
lean_dec(x_552);
x_564 = l_Lean_Expr_forallE___override(x_548, x_544, x_546, x_551);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_547);
return x_565;
}
else
{
lean_object* x_566; 
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_544);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_552);
lean_ctor_set(x_566, 1, x_547);
return x_566;
}
}
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_1);
x_567 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_568 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_567);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_547);
return x_569;
}
}
block_604:
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_571);
x_572 = lean_st_ref_get(x_3, x_545);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
lean_inc(x_543);
x_576 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_575, x_543);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; 
lean_inc(x_543);
x_577 = l_Lean_Meta_Closure_collectExprAux(x_543, x_2, x_3, x_4, x_5, x_6, x_7, x_574);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_580 = lean_st_ref_take(x_3, x_579);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_581, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_inc(x_578);
x_585 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_584, x_543, x_578);
x_586 = lean_ctor_get(x_581, 2);
lean_inc(x_586);
x_587 = lean_ctor_get(x_581, 3);
lean_inc(x_587);
x_588 = lean_ctor_get(x_581, 4);
lean_inc(x_588);
x_589 = lean_ctor_get(x_581, 5);
lean_inc(x_589);
x_590 = lean_ctor_get(x_581, 6);
lean_inc(x_590);
x_591 = lean_ctor_get(x_581, 7);
lean_inc(x_591);
x_592 = lean_ctor_get(x_581, 8);
lean_inc(x_592);
x_593 = lean_ctor_get(x_581, 9);
lean_inc(x_593);
x_594 = lean_ctor_get(x_581, 10);
lean_inc(x_594);
x_595 = lean_ctor_get(x_581, 11);
lean_inc(x_595);
lean_dec(x_581);
x_596 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_596, 0, x_583);
lean_ctor_set(x_596, 1, x_585);
lean_ctor_set(x_596, 2, x_586);
lean_ctor_set(x_596, 3, x_587);
lean_ctor_set(x_596, 4, x_588);
lean_ctor_set(x_596, 5, x_589);
lean_ctor_set(x_596, 6, x_590);
lean_ctor_set(x_596, 7, x_591);
lean_ctor_set(x_596, 8, x_592);
lean_ctor_set(x_596, 9, x_593);
lean_ctor_set(x_596, 10, x_594);
lean_ctor_set(x_596, 11, x_595);
x_597 = lean_st_ref_set(x_3, x_596, x_582);
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
lean_dec(x_597);
x_546 = x_578;
x_547 = x_598;
goto block_570;
}
else
{
uint8_t x_599; 
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_577);
if (x_599 == 0)
{
return x_577;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_577, 0);
x_601 = lean_ctor_get(x_577, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_577);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
else
{
lean_object* x_603; 
lean_dec(x_543);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_603 = lean_ctor_get(x_576, 0);
lean_inc(x_603);
lean_dec(x_576);
x_546 = x_603;
x_547 = x_574;
goto block_570;
}
}
}
block_645:
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_612);
x_613 = lean_st_ref_get(x_3, x_8);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
lean_inc(x_542);
x_617 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_616, x_542);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_542);
x_618 = l_Lean_Meta_Closure_collectExprAux(x_542, x_2, x_3, x_4, x_5, x_6, x_7, x_615);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec(x_618);
x_621 = lean_st_ref_take(x_3, x_620);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_ctor_get(x_622, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_622, 1);
lean_inc(x_625);
lean_inc(x_619);
x_626 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_625, x_542, x_619);
x_627 = lean_ctor_get(x_622, 2);
lean_inc(x_627);
x_628 = lean_ctor_get(x_622, 3);
lean_inc(x_628);
x_629 = lean_ctor_get(x_622, 4);
lean_inc(x_629);
x_630 = lean_ctor_get(x_622, 5);
lean_inc(x_630);
x_631 = lean_ctor_get(x_622, 6);
lean_inc(x_631);
x_632 = lean_ctor_get(x_622, 7);
lean_inc(x_632);
x_633 = lean_ctor_get(x_622, 8);
lean_inc(x_633);
x_634 = lean_ctor_get(x_622, 9);
lean_inc(x_634);
x_635 = lean_ctor_get(x_622, 10);
lean_inc(x_635);
x_636 = lean_ctor_get(x_622, 11);
lean_inc(x_636);
lean_dec(x_622);
x_637 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_637, 0, x_624);
lean_ctor_set(x_637, 1, x_626);
lean_ctor_set(x_637, 2, x_627);
lean_ctor_set(x_637, 3, x_628);
lean_ctor_set(x_637, 4, x_629);
lean_ctor_set(x_637, 5, x_630);
lean_ctor_set(x_637, 6, x_631);
lean_ctor_set(x_637, 7, x_632);
lean_ctor_set(x_637, 8, x_633);
lean_ctor_set(x_637, 9, x_634);
lean_ctor_set(x_637, 10, x_635);
lean_ctor_set(x_637, 11, x_636);
x_638 = lean_st_ref_set(x_3, x_637, x_623);
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_544 = x_619;
x_545 = x_639;
goto block_611;
}
else
{
uint8_t x_640; 
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_618);
if (x_640 == 0)
{
return x_618;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_618, 0);
x_642 = lean_ctor_get(x_618, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_618);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
else
{
lean_object* x_644; 
lean_dec(x_542);
x_644 = lean_ctor_get(x_617, 0);
lean_inc(x_644);
lean_dec(x_617);
x_544 = x_644;
x_545 = x_615;
goto block_611;
}
}
}
case 8:
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_768; uint8_t x_802; 
x_652 = lean_ctor_get(x_1, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_1, 2);
lean_inc(x_653);
x_654 = lean_ctor_get(x_1, 3);
lean_inc(x_654);
x_802 = l_Lean_Expr_hasLevelParam(x_652);
if (x_802 == 0)
{
uint8_t x_803; 
x_803 = l_Lean_Expr_hasFVar(x_652);
if (x_803 == 0)
{
uint8_t x_804; 
x_804 = l_Lean_Expr_hasMVar(x_652);
if (x_804 == 0)
{
x_655 = x_652;
x_656 = x_8;
goto block_767;
}
else
{
lean_object* x_805; 
x_805 = lean_box(0);
x_768 = x_805;
goto block_801;
}
}
else
{
lean_object* x_806; 
x_806 = lean_box(0);
x_768 = x_806;
goto block_801;
}
}
else
{
lean_object* x_807; 
x_807 = lean_box(0);
x_768 = x_807;
goto block_801;
}
block_767:
{
lean_object* x_657; lean_object* x_658; lean_object* x_727; uint8_t x_761; 
x_761 = l_Lean_Expr_hasLevelParam(x_653);
if (x_761 == 0)
{
uint8_t x_762; 
x_762 = l_Lean_Expr_hasFVar(x_653);
if (x_762 == 0)
{
uint8_t x_763; 
x_763 = l_Lean_Expr_hasMVar(x_653);
if (x_763 == 0)
{
x_657 = x_653;
x_658 = x_656;
goto block_726;
}
else
{
lean_object* x_764; 
x_764 = lean_box(0);
x_727 = x_764;
goto block_760;
}
}
else
{
lean_object* x_765; 
x_765 = lean_box(0);
x_727 = x_765;
goto block_760;
}
}
else
{
lean_object* x_766; 
x_766 = lean_box(0);
x_727 = x_766;
goto block_760;
}
block_726:
{
lean_object* x_659; lean_object* x_660; lean_object* x_686; uint8_t x_720; 
x_720 = l_Lean_Expr_hasLevelParam(x_654);
if (x_720 == 0)
{
uint8_t x_721; 
x_721 = l_Lean_Expr_hasFVar(x_654);
if (x_721 == 0)
{
uint8_t x_722; 
x_722 = l_Lean_Expr_hasMVar(x_654);
if (x_722 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_659 = x_654;
x_660 = x_658;
goto block_685;
}
else
{
lean_object* x_723; 
x_723 = lean_box(0);
x_686 = x_723;
goto block_719;
}
}
else
{
lean_object* x_724; 
x_724 = lean_box(0);
x_686 = x_724;
goto block_719;
}
}
else
{
lean_object* x_725; 
x_725 = lean_box(0);
x_686 = x_725;
goto block_719;
}
block_685:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; size_t x_666; size_t x_667; uint8_t x_668; 
x_661 = lean_ctor_get(x_1, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_1, 1);
lean_inc(x_662);
x_663 = lean_ctor_get(x_1, 2);
lean_inc(x_663);
x_664 = lean_ctor_get(x_1, 3);
lean_inc(x_664);
x_665 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_666 = lean_ptr_addr(x_662);
lean_dec(x_662);
x_667 = lean_ptr_addr(x_655);
x_668 = lean_usize_dec_eq(x_666, x_667);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_1);
x_669 = l_Lean_Expr_letE___override(x_661, x_655, x_657, x_659, x_665);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_660);
return x_670;
}
else
{
size_t x_671; size_t x_672; uint8_t x_673; 
x_671 = lean_ptr_addr(x_663);
lean_dec(x_663);
x_672 = lean_ptr_addr(x_657);
x_673 = lean_usize_dec_eq(x_671, x_672);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_664);
lean_dec(x_1);
x_674 = l_Lean_Expr_letE___override(x_661, x_655, x_657, x_659, x_665);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_660);
return x_675;
}
else
{
size_t x_676; size_t x_677; uint8_t x_678; 
x_676 = lean_ptr_addr(x_664);
lean_dec(x_664);
x_677 = lean_ptr_addr(x_659);
x_678 = lean_usize_dec_eq(x_676, x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_1);
x_679 = l_Lean_Expr_letE___override(x_661, x_655, x_657, x_659, x_665);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_660);
return x_680;
}
else
{
lean_object* x_681; 
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_657);
lean_dec(x_655);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_1);
lean_ctor_set(x_681, 1, x_660);
return x_681;
}
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_659);
lean_dec(x_657);
lean_dec(x_655);
lean_dec(x_1);
x_682 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_683 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_682);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_660);
return x_684;
}
}
block_719:
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_686);
x_687 = lean_st_ref_get(x_3, x_658);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
lean_inc(x_654);
x_691 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_690, x_654);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; 
lean_inc(x_654);
x_692 = l_Lean_Meta_Closure_collectExprAux(x_654, x_2, x_3, x_4, x_5, x_6, x_7, x_689);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_st_ref_take(x_3, x_694);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_696, 1);
lean_inc(x_699);
lean_inc(x_693);
x_700 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_699, x_654, x_693);
x_701 = lean_ctor_get(x_696, 2);
lean_inc(x_701);
x_702 = lean_ctor_get(x_696, 3);
lean_inc(x_702);
x_703 = lean_ctor_get(x_696, 4);
lean_inc(x_703);
x_704 = lean_ctor_get(x_696, 5);
lean_inc(x_704);
x_705 = lean_ctor_get(x_696, 6);
lean_inc(x_705);
x_706 = lean_ctor_get(x_696, 7);
lean_inc(x_706);
x_707 = lean_ctor_get(x_696, 8);
lean_inc(x_707);
x_708 = lean_ctor_get(x_696, 9);
lean_inc(x_708);
x_709 = lean_ctor_get(x_696, 10);
lean_inc(x_709);
x_710 = lean_ctor_get(x_696, 11);
lean_inc(x_710);
lean_dec(x_696);
x_711 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_711, 0, x_698);
lean_ctor_set(x_711, 1, x_700);
lean_ctor_set(x_711, 2, x_701);
lean_ctor_set(x_711, 3, x_702);
lean_ctor_set(x_711, 4, x_703);
lean_ctor_set(x_711, 5, x_704);
lean_ctor_set(x_711, 6, x_705);
lean_ctor_set(x_711, 7, x_706);
lean_ctor_set(x_711, 8, x_707);
lean_ctor_set(x_711, 9, x_708);
lean_ctor_set(x_711, 10, x_709);
lean_ctor_set(x_711, 11, x_710);
x_712 = lean_st_ref_set(x_3, x_711, x_697);
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
lean_dec(x_712);
x_659 = x_693;
x_660 = x_713;
goto block_685;
}
else
{
uint8_t x_714; 
lean_dec(x_657);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_1);
x_714 = !lean_is_exclusive(x_692);
if (x_714 == 0)
{
return x_692;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_692, 0);
x_716 = lean_ctor_get(x_692, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_692);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
else
{
lean_object* x_718; 
lean_dec(x_654);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_718 = lean_ctor_get(x_691, 0);
lean_inc(x_718);
lean_dec(x_691);
x_659 = x_718;
x_660 = x_689;
goto block_685;
}
}
}
block_760:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_727);
x_728 = lean_st_ref_get(x_3, x_656);
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
lean_inc(x_653);
x_732 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_731, x_653);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_653);
x_733 = l_Lean_Meta_Closure_collectExprAux(x_653, x_2, x_3, x_4, x_5, x_6, x_7, x_730);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = lean_st_ref_take(x_3, x_735);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec(x_736);
x_739 = lean_ctor_get(x_737, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_737, 1);
lean_inc(x_740);
lean_inc(x_734);
x_741 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_740, x_653, x_734);
x_742 = lean_ctor_get(x_737, 2);
lean_inc(x_742);
x_743 = lean_ctor_get(x_737, 3);
lean_inc(x_743);
x_744 = lean_ctor_get(x_737, 4);
lean_inc(x_744);
x_745 = lean_ctor_get(x_737, 5);
lean_inc(x_745);
x_746 = lean_ctor_get(x_737, 6);
lean_inc(x_746);
x_747 = lean_ctor_get(x_737, 7);
lean_inc(x_747);
x_748 = lean_ctor_get(x_737, 8);
lean_inc(x_748);
x_749 = lean_ctor_get(x_737, 9);
lean_inc(x_749);
x_750 = lean_ctor_get(x_737, 10);
lean_inc(x_750);
x_751 = lean_ctor_get(x_737, 11);
lean_inc(x_751);
lean_dec(x_737);
x_752 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_752, 0, x_739);
lean_ctor_set(x_752, 1, x_741);
lean_ctor_set(x_752, 2, x_742);
lean_ctor_set(x_752, 3, x_743);
lean_ctor_set(x_752, 4, x_744);
lean_ctor_set(x_752, 5, x_745);
lean_ctor_set(x_752, 6, x_746);
lean_ctor_set(x_752, 7, x_747);
lean_ctor_set(x_752, 8, x_748);
lean_ctor_set(x_752, 9, x_749);
lean_ctor_set(x_752, 10, x_750);
lean_ctor_set(x_752, 11, x_751);
x_753 = lean_st_ref_set(x_3, x_752, x_738);
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
lean_dec(x_753);
x_657 = x_734;
x_658 = x_754;
goto block_726;
}
else
{
uint8_t x_755; 
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_755 = !lean_is_exclusive(x_733);
if (x_755 == 0)
{
return x_733;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_733, 0);
x_757 = lean_ctor_get(x_733, 1);
lean_inc(x_757);
lean_inc(x_756);
lean_dec(x_733);
x_758 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_758, 0, x_756);
lean_ctor_set(x_758, 1, x_757);
return x_758;
}
}
}
else
{
lean_object* x_759; 
lean_dec(x_653);
x_759 = lean_ctor_get(x_732, 0);
lean_inc(x_759);
lean_dec(x_732);
x_657 = x_759;
x_658 = x_730;
goto block_726;
}
}
}
block_801:
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_768);
x_769 = lean_st_ref_get(x_3, x_8);
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
lean_inc(x_652);
x_773 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_772, x_652);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_652);
x_774 = l_Lean_Meta_Closure_collectExprAux(x_652, x_2, x_3, x_4, x_5, x_6, x_7, x_771);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_777 = lean_st_ref_take(x_3, x_776);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_780 = lean_ctor_get(x_778, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_778, 1);
lean_inc(x_781);
lean_inc(x_775);
x_782 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_781, x_652, x_775);
x_783 = lean_ctor_get(x_778, 2);
lean_inc(x_783);
x_784 = lean_ctor_get(x_778, 3);
lean_inc(x_784);
x_785 = lean_ctor_get(x_778, 4);
lean_inc(x_785);
x_786 = lean_ctor_get(x_778, 5);
lean_inc(x_786);
x_787 = lean_ctor_get(x_778, 6);
lean_inc(x_787);
x_788 = lean_ctor_get(x_778, 7);
lean_inc(x_788);
x_789 = lean_ctor_get(x_778, 8);
lean_inc(x_789);
x_790 = lean_ctor_get(x_778, 9);
lean_inc(x_790);
x_791 = lean_ctor_get(x_778, 10);
lean_inc(x_791);
x_792 = lean_ctor_get(x_778, 11);
lean_inc(x_792);
lean_dec(x_778);
x_793 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_793, 0, x_780);
lean_ctor_set(x_793, 1, x_782);
lean_ctor_set(x_793, 2, x_783);
lean_ctor_set(x_793, 3, x_784);
lean_ctor_set(x_793, 4, x_785);
lean_ctor_set(x_793, 5, x_786);
lean_ctor_set(x_793, 6, x_787);
lean_ctor_set(x_793, 7, x_788);
lean_ctor_set(x_793, 8, x_789);
lean_ctor_set(x_793, 9, x_790);
lean_ctor_set(x_793, 10, x_791);
lean_ctor_set(x_793, 11, x_792);
x_794 = lean_st_ref_set(x_3, x_793, x_779);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec(x_794);
x_655 = x_775;
x_656 = x_795;
goto block_767;
}
else
{
uint8_t x_796; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_796 = !lean_is_exclusive(x_774);
if (x_796 == 0)
{
return x_774;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_774, 0);
x_798 = lean_ctor_get(x_774, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_774);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
else
{
lean_object* x_800; 
lean_dec(x_652);
x_800 = lean_ctor_get(x_773, 0);
lean_inc(x_800);
lean_dec(x_773);
x_655 = x_800;
x_656 = x_771;
goto block_767;
}
}
}
case 10:
{
lean_object* x_808; lean_object* x_809; uint8_t x_843; 
x_808 = lean_ctor_get(x_1, 1);
lean_inc(x_808);
x_843 = l_Lean_Expr_hasLevelParam(x_808);
if (x_843 == 0)
{
uint8_t x_844; 
x_844 = l_Lean_Expr_hasFVar(x_808);
if (x_844 == 0)
{
uint8_t x_845; 
x_845 = l_Lean_Expr_hasMVar(x_808);
if (x_845 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_808;
x_10 = x_8;
goto block_22;
}
else
{
lean_object* x_846; 
x_846 = lean_box(0);
x_809 = x_846;
goto block_842;
}
}
else
{
lean_object* x_847; 
x_847 = lean_box(0);
x_809 = x_847;
goto block_842;
}
}
else
{
lean_object* x_848; 
x_848 = lean_box(0);
x_809 = x_848;
goto block_842;
}
block_842:
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_809);
x_810 = lean_st_ref_get(x_3, x_8);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
lean_inc(x_808);
x_814 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_813, x_808);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; 
lean_inc(x_808);
x_815 = l_Lean_Meta_Closure_collectExprAux(x_808, x_2, x_3, x_4, x_5, x_6, x_7, x_812);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = lean_st_ref_take(x_3, x_817);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
x_821 = lean_ctor_get(x_819, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_819, 1);
lean_inc(x_822);
lean_inc(x_816);
x_823 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_822, x_808, x_816);
x_824 = lean_ctor_get(x_819, 2);
lean_inc(x_824);
x_825 = lean_ctor_get(x_819, 3);
lean_inc(x_825);
x_826 = lean_ctor_get(x_819, 4);
lean_inc(x_826);
x_827 = lean_ctor_get(x_819, 5);
lean_inc(x_827);
x_828 = lean_ctor_get(x_819, 6);
lean_inc(x_828);
x_829 = lean_ctor_get(x_819, 7);
lean_inc(x_829);
x_830 = lean_ctor_get(x_819, 8);
lean_inc(x_830);
x_831 = lean_ctor_get(x_819, 9);
lean_inc(x_831);
x_832 = lean_ctor_get(x_819, 10);
lean_inc(x_832);
x_833 = lean_ctor_get(x_819, 11);
lean_inc(x_833);
lean_dec(x_819);
x_834 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_834, 0, x_821);
lean_ctor_set(x_834, 1, x_823);
lean_ctor_set(x_834, 2, x_824);
lean_ctor_set(x_834, 3, x_825);
lean_ctor_set(x_834, 4, x_826);
lean_ctor_set(x_834, 5, x_827);
lean_ctor_set(x_834, 6, x_828);
lean_ctor_set(x_834, 7, x_829);
lean_ctor_set(x_834, 8, x_830);
lean_ctor_set(x_834, 9, x_831);
lean_ctor_set(x_834, 10, x_832);
lean_ctor_set(x_834, 11, x_833);
x_835 = lean_st_ref_set(x_3, x_834, x_820);
x_836 = lean_ctor_get(x_835, 1);
lean_inc(x_836);
lean_dec(x_835);
x_9 = x_816;
x_10 = x_836;
goto block_22;
}
else
{
uint8_t x_837; 
lean_dec(x_808);
lean_dec(x_1);
x_837 = !lean_is_exclusive(x_815);
if (x_837 == 0)
{
return x_815;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_815, 0);
x_839 = lean_ctor_get(x_815, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_815);
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
return x_840;
}
}
}
else
{
lean_object* x_841; 
lean_dec(x_808);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_841 = lean_ctor_get(x_814, 0);
lean_inc(x_841);
lean_dec(x_814);
x_9 = x_841;
x_10 = x_812;
goto block_22;
}
}
}
case 11:
{
lean_object* x_849; lean_object* x_850; uint8_t x_884; 
x_849 = lean_ctor_get(x_1, 2);
lean_inc(x_849);
x_884 = l_Lean_Expr_hasLevelParam(x_849);
if (x_884 == 0)
{
uint8_t x_885; 
x_885 = l_Lean_Expr_hasFVar(x_849);
if (x_885 == 0)
{
uint8_t x_886; 
x_886 = l_Lean_Expr_hasMVar(x_849);
if (x_886 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = x_849;
x_24 = x_8;
goto block_37;
}
else
{
lean_object* x_887; 
x_887 = lean_box(0);
x_850 = x_887;
goto block_883;
}
}
else
{
lean_object* x_888; 
x_888 = lean_box(0);
x_850 = x_888;
goto block_883;
}
}
else
{
lean_object* x_889; 
x_889 = lean_box(0);
x_850 = x_889;
goto block_883;
}
block_883:
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_850);
x_851 = lean_st_ref_get(x_3, x_8);
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
lean_inc(x_849);
x_855 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_854, x_849);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; 
lean_inc(x_849);
x_856 = l_Lean_Meta_Closure_collectExprAux(x_849, x_2, x_3, x_4, x_5, x_6, x_7, x_853);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_856, 1);
lean_inc(x_858);
lean_dec(x_856);
x_859 = lean_st_ref_take(x_3, x_858);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
x_862 = lean_ctor_get(x_860, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_860, 1);
lean_inc(x_863);
lean_inc(x_857);
x_864 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_863, x_849, x_857);
x_865 = lean_ctor_get(x_860, 2);
lean_inc(x_865);
x_866 = lean_ctor_get(x_860, 3);
lean_inc(x_866);
x_867 = lean_ctor_get(x_860, 4);
lean_inc(x_867);
x_868 = lean_ctor_get(x_860, 5);
lean_inc(x_868);
x_869 = lean_ctor_get(x_860, 6);
lean_inc(x_869);
x_870 = lean_ctor_get(x_860, 7);
lean_inc(x_870);
x_871 = lean_ctor_get(x_860, 8);
lean_inc(x_871);
x_872 = lean_ctor_get(x_860, 9);
lean_inc(x_872);
x_873 = lean_ctor_get(x_860, 10);
lean_inc(x_873);
x_874 = lean_ctor_get(x_860, 11);
lean_inc(x_874);
lean_dec(x_860);
x_875 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_875, 0, x_862);
lean_ctor_set(x_875, 1, x_864);
lean_ctor_set(x_875, 2, x_865);
lean_ctor_set(x_875, 3, x_866);
lean_ctor_set(x_875, 4, x_867);
lean_ctor_set(x_875, 5, x_868);
lean_ctor_set(x_875, 6, x_869);
lean_ctor_set(x_875, 7, x_870);
lean_ctor_set(x_875, 8, x_871);
lean_ctor_set(x_875, 9, x_872);
lean_ctor_set(x_875, 10, x_873);
lean_ctor_set(x_875, 11, x_874);
x_876 = lean_st_ref_set(x_3, x_875, x_861);
x_877 = lean_ctor_get(x_876, 1);
lean_inc(x_877);
lean_dec(x_876);
x_23 = x_857;
x_24 = x_877;
goto block_37;
}
else
{
uint8_t x_878; 
lean_dec(x_849);
lean_dec(x_1);
x_878 = !lean_is_exclusive(x_856);
if (x_878 == 0)
{
return x_856;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_856, 0);
x_880 = lean_ctor_get(x_856, 1);
lean_inc(x_880);
lean_inc(x_879);
lean_dec(x_856);
x_881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
return x_881;
}
}
}
else
{
lean_object* x_882; 
lean_dec(x_849);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_882 = lean_ctor_get(x_855, 0);
lean_inc(x_882);
lean_dec(x_855);
x_23 = x_882;
x_24 = x_853;
goto block_37;
}
}
}
default: 
{
lean_object* x_890; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_890 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_890, 0, x_1);
lean_ctor_set(x_890, 1, x_8);
return x_890;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_93; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_93 = l_Lean_Expr_hasLevelParam(x_11);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasFVar(x_11);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasMVar(x_11);
if (x_95 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_96; 
lean_free_object(x_9);
x_96 = lean_box(0);
x_13 = x_96;
goto block_92;
}
}
else
{
lean_object* x_97; 
lean_free_object(x_9);
x_97 = lean_box(0);
x_13 = x_97;
goto block_92;
}
}
else
{
lean_object* x_98; 
lean_free_object(x_9);
x_98 = lean_box(0);
x_13 = x_98;
goto block_92;
}
block_92:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_3, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_18, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_inc(x_11);
x_20 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
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
x_28 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_27, x_11, x_21);
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
x_46 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_35, x_11, x_21);
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
lean_dec(x_11);
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
lean_dec(x_11);
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
lean_inc(x_11);
x_60 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_59, x_11);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_inc(x_11);
x_61 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
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
x_80 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_68, x_11, x_62);
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
lean_dec(x_11);
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
lean_dec(x_11);
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
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_140; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_9);
x_140 = l_Lean_Expr_hasLevelParam(x_99);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_hasFVar(x_99);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Expr_hasMVar(x_99);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_99);
lean_ctor_set(x_143, 1, x_100);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_101 = x_144;
goto block_139;
}
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_101 = x_145;
goto block_139;
}
}
else
{
lean_object* x_146; 
x_146 = lean_box(0);
x_101 = x_146;
goto block_139;
}
block_139:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
x_102 = lean_st_ref_get(x_3, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
lean_inc(x_99);
x_107 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_106, x_99);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_inc(x_99);
x_108 = l_Lean_Meta_Closure_collectExprAux(x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_st_ref_take(x_3, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 6);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 7);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 8);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 9);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 10);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 11);
lean_inc(x_125);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 lean_ctor_release(x_112, 6);
 lean_ctor_release(x_112, 7);
 lean_ctor_release(x_112, 8);
 lean_ctor_release(x_112, 9);
 lean_ctor_release(x_112, 10);
 lean_ctor_release(x_112, 11);
 x_126 = x_112;
} else {
 lean_dec_ref(x_112);
 x_126 = lean_box(0);
}
lean_inc(x_109);
x_127 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_115, x_99, x_109);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 12, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_116);
lean_ctor_set(x_128, 3, x_117);
lean_ctor_set(x_128, 4, x_118);
lean_ctor_set(x_128, 5, x_119);
lean_ctor_set(x_128, 6, x_120);
lean_ctor_set(x_128, 7, x_121);
lean_ctor_set(x_128, 8, x_122);
lean_ctor_set(x_128, 9, x_123);
lean_ctor_set(x_128, 10, x_124);
lean_ctor_set(x_128, 11, x_125);
x_129 = lean_st_ref_set(x_3, x_128, x_113);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_109);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_99);
x_133 = lean_ctor_get(x_108, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_99);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_107, 0);
lean_inc(x_137);
lean_dec(x_107);
if (lean_is_scalar(x_105)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_105;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_104);
return x_138;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_147 = !lean_is_exclusive(x_9);
if (x_147 == 0)
{
return x_9;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_9, 0);
x_149 = lean_ctor_get(x_9, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_9);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
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
x_43 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
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
lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_76, 5);
x_80 = lean_array_get_size(x_79);
x_81 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_82 = 0;
x_83 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_81, x_82, x_79);
lean_dec(x_62);
lean_ctor_set(x_76, 5, x_83);
x_84 = lean_st_ref_set(x_2, x_76, x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_7 = x_85;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
x_89 = lean_ctor_get(x_76, 2);
x_90 = lean_ctor_get(x_76, 3);
x_91 = lean_ctor_get(x_76, 4);
x_92 = lean_ctor_get(x_76, 5);
x_93 = lean_ctor_get(x_76, 6);
x_94 = lean_ctor_get(x_76, 7);
x_95 = lean_ctor_get(x_76, 8);
x_96 = lean_ctor_get(x_76, 9);
x_97 = lean_ctor_get(x_76, 10);
x_98 = lean_ctor_get(x_76, 11);
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
lean_inc(x_87);
lean_dec(x_76);
x_99 = lean_array_get_size(x_92);
x_100 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_101 = 0;
x_102 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_100, x_101, x_92);
lean_dec(x_62);
x_103 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_88);
lean_ctor_set(x_103, 2, x_89);
lean_ctor_set(x_103, 3, x_90);
lean_ctor_set(x_103, 4, x_91);
lean_ctor_set(x_103, 5, x_102);
lean_ctor_set(x_103, 6, x_93);
lean_ctor_set(x_103, 7, x_94);
lean_ctor_set(x_103, 8, x_95);
lean_ctor_set(x_103, 9, x_96);
lean_ctor_set(x_103, 10, x_97);
lean_ctor_set(x_103, 11, x_98);
x_104 = lean_st_ref_set(x_2, x_103, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_7 = x_105;
goto _start;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_107 = lean_ctor_get(x_65, 0);
x_108 = lean_ctor_get(x_65, 1);
x_109 = lean_ctor_get(x_65, 2);
x_110 = lean_ctor_get(x_65, 3);
x_111 = lean_ctor_get(x_65, 4);
x_112 = lean_ctor_get(x_65, 5);
x_113 = lean_ctor_get(x_65, 6);
x_114 = lean_ctor_get(x_65, 7);
x_115 = lean_ctor_get(x_65, 8);
x_116 = lean_ctor_get(x_65, 9);
x_117 = lean_ctor_get(x_65, 10);
x_118 = lean_ctor_get(x_65, 11);
lean_inc(x_118);
lean_inc(x_117);
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
lean_dec(x_65);
x_119 = lean_unsigned_to_nat(0u);
x_120 = 0;
x_121 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_119);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_120);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_121);
x_122 = lean_array_push(x_114, x_21);
x_123 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_123, 0, x_107);
lean_ctor_set(x_123, 1, x_108);
lean_ctor_set(x_123, 2, x_109);
lean_ctor_set(x_123, 3, x_110);
lean_ctor_set(x_123, 4, x_111);
lean_ctor_set(x_123, 5, x_112);
lean_ctor_set(x_123, 6, x_113);
lean_ctor_set(x_123, 7, x_122);
lean_ctor_set(x_123, 8, x_115);
lean_ctor_set(x_123, 9, x_116);
lean_ctor_set(x_123, 10, x_117);
lean_ctor_set(x_123, 11, x_118);
x_124 = lean_st_ref_set(x_2, x_123, x_66);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_st_ref_take(x_2, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 5);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 6);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 7);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 8);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 9);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 10);
lean_inc(x_139);
x_140 = lean_ctor_get(x_127, 11);
lean_inc(x_140);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 lean_ctor_release(x_127, 8);
 lean_ctor_release(x_127, 9);
 lean_ctor_release(x_127, 10);
 lean_ctor_release(x_127, 11);
 x_141 = x_127;
} else {
 lean_dec_ref(x_127);
 x_141 = lean_box(0);
}
x_142 = lean_array_get_size(x_134);
x_143 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_144 = 0;
x_145 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_143, x_144, x_134);
lean_dec(x_62);
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(0, 12, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_132);
lean_ctor_set(x_146, 4, x_133);
lean_ctor_set(x_146, 5, x_145);
lean_ctor_set(x_146, 6, x_135);
lean_ctor_set(x_146, 7, x_136);
lean_ctor_set(x_146, 8, x_137);
lean_ctor_set(x_146, 9, x_138);
lean_ctor_set(x_146, 10, x_139);
lean_ctor_set(x_146, 11, x_140);
x_147 = lean_st_ref_set(x_2, x_146, x_128);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_7 = x_148;
goto _start;
}
}
else
{
uint8_t x_150; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_61);
if (x_150 == 0)
{
return x_61;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_61, 0);
x_152 = lean_ctor_get(x_61, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_61);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_58);
if (x_154 == 0)
{
return x_58;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_58, 0);
x_156 = lean_ctor_get(x_58, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_58);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_21, 2);
x_159 = lean_ctor_get(x_21, 3);
x_160 = lean_ctor_get(x_21, 4);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_21);
x_161 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_162, x_18);
lean_dec(x_162);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; lean_object* x_166; 
lean_dec(x_160);
x_165 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_166 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_158, x_159, x_165, x_1, x_2, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_Expr_fvar___override(x_18);
x_169 = l_Lean_Meta_Closure_pushFVarArg(x_168, x_1, x_2, x_3, x_4, x_5, x_6, x_167);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_7 = x_170;
goto _start;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_174 = x_166;
} else {
 lean_dec_ref(x_166);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_164);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_176 = l_Lean_Meta_Closure_collectExpr(x_159, x_1, x_2, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_179 = l_Lean_Meta_Closure_collectExpr(x_160, x_1, x_2, x_3, x_4, x_5, x_6, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; size_t x_223; size_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_st_ref_take(x_2, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 5);
lean_inc(x_190);
x_191 = lean_ctor_get(x_183, 6);
lean_inc(x_191);
x_192 = lean_ctor_get(x_183, 7);
lean_inc(x_192);
x_193 = lean_ctor_get(x_183, 8);
lean_inc(x_193);
x_194 = lean_ctor_get(x_183, 9);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 10);
lean_inc(x_195);
x_196 = lean_ctor_get(x_183, 11);
lean_inc(x_196);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 lean_ctor_release(x_183, 6);
 lean_ctor_release(x_183, 7);
 lean_ctor_release(x_183, 8);
 lean_ctor_release(x_183, 9);
 lean_ctor_release(x_183, 10);
 lean_ctor_release(x_183, 11);
 x_197 = x_183;
} else {
 lean_dec_ref(x_183);
 x_197 = lean_box(0);
}
x_198 = lean_unsigned_to_nat(0u);
x_199 = 0;
x_200 = 0;
lean_inc(x_180);
lean_inc(x_19);
x_201 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_19);
lean_ctor_set(x_201, 2, x_158);
lean_ctor_set(x_201, 3, x_177);
lean_ctor_set(x_201, 4, x_180);
lean_ctor_set_uint8(x_201, sizeof(void*)*5, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*5 + 1, x_200);
x_202 = lean_array_push(x_192, x_201);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 12, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_185);
lean_ctor_set(x_203, 1, x_186);
lean_ctor_set(x_203, 2, x_187);
lean_ctor_set(x_203, 3, x_188);
lean_ctor_set(x_203, 4, x_189);
lean_ctor_set(x_203, 5, x_190);
lean_ctor_set(x_203, 6, x_191);
lean_ctor_set(x_203, 7, x_202);
lean_ctor_set(x_203, 8, x_193);
lean_ctor_set(x_203, 9, x_194);
lean_ctor_set(x_203, 10, x_195);
lean_ctor_set(x_203, 11, x_196);
x_204 = lean_st_ref_set(x_2, x_203, x_184);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = lean_st_ref_take(x_2, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_207, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_207, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_207, 5);
lean_inc(x_214);
x_215 = lean_ctor_get(x_207, 6);
lean_inc(x_215);
x_216 = lean_ctor_get(x_207, 7);
lean_inc(x_216);
x_217 = lean_ctor_get(x_207, 8);
lean_inc(x_217);
x_218 = lean_ctor_get(x_207, 9);
lean_inc(x_218);
x_219 = lean_ctor_get(x_207, 10);
lean_inc(x_219);
x_220 = lean_ctor_get(x_207, 11);
lean_inc(x_220);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 lean_ctor_release(x_207, 6);
 lean_ctor_release(x_207, 7);
 lean_ctor_release(x_207, 8);
 lean_ctor_release(x_207, 9);
 lean_ctor_release(x_207, 10);
 lean_ctor_release(x_207, 11);
 x_221 = x_207;
} else {
 lean_dec_ref(x_207);
 x_221 = lean_box(0);
}
x_222 = lean_array_get_size(x_214);
x_223 = lean_usize_of_nat(x_222);
lean_dec(x_222);
x_224 = 0;
x_225 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_180, x_223, x_224, x_214);
lean_dec(x_180);
if (lean_is_scalar(x_221)) {
 x_226 = lean_alloc_ctor(0, 12, 0);
} else {
 x_226 = x_221;
}
lean_ctor_set(x_226, 0, x_209);
lean_ctor_set(x_226, 1, x_210);
lean_ctor_set(x_226, 2, x_211);
lean_ctor_set(x_226, 3, x_212);
lean_ctor_set(x_226, 4, x_213);
lean_ctor_set(x_226, 5, x_225);
lean_ctor_set(x_226, 6, x_215);
lean_ctor_set(x_226, 7, x_216);
lean_ctor_set(x_226, 8, x_217);
lean_ctor_set(x_226, 9, x_218);
lean_ctor_set(x_226, 10, x_219);
lean_ctor_set(x_226, 11, x_220);
x_227 = lean_st_ref_set(x_2, x_226, x_208);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_7 = x_228;
goto _start;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_177);
lean_dec(x_158);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_179, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_179, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_232 = x_179;
} else {
 lean_dec_ref(x_179);
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
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_234 = lean_ctor_get(x_176, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_176, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_236 = x_176;
} else {
 lean_dec_ref(x_176);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_20);
if (x_238 == 0)
{
return x_20;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_20, 0);
x_240 = lean_ctor_get(x_20, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_20);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
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
lean_ctor_set_uint8(x_11, 10, x_16);
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
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
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
lean_dec(x_11);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_54, 0, x_42);
lean_ctor_set_uint8(x_54, 1, x_43);
lean_ctor_set_uint8(x_54, 2, x_44);
lean_ctor_set_uint8(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, 4, x_46);
lean_ctor_set_uint8(x_54, 5, x_47);
lean_ctor_set_uint8(x_54, 6, x_48);
lean_ctor_set_uint8(x_54, 7, x_49);
lean_ctor_set_uint8(x_54, 8, x_50);
lean_ctor_set_uint8(x_54, 9, x_51);
lean_ctor_set_uint8(x_54, 10, x_53);
lean_ctor_set_uint8(x_54, 11, x_52);
lean_ctor_set(x_5, 0, x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_59);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
lean_dec(x_56);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_72 = x_58;
} else {
 lean_dec_ref(x_58);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_76 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_78 = lean_ctor_get(x_5, 1);
x_79 = lean_ctor_get(x_5, 2);
x_80 = lean_ctor_get(x_5, 3);
x_81 = lean_ctor_get(x_5, 4);
x_82 = lean_ctor_get(x_5, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_83 = lean_ctor_get_uint8(x_11, 0);
x_84 = lean_ctor_get_uint8(x_11, 1);
x_85 = lean_ctor_get_uint8(x_11, 2);
x_86 = lean_ctor_get_uint8(x_11, 3);
x_87 = lean_ctor_get_uint8(x_11, 4);
x_88 = lean_ctor_get_uint8(x_11, 5);
x_89 = lean_ctor_get_uint8(x_11, 6);
x_90 = lean_ctor_get_uint8(x_11, 7);
x_91 = lean_ctor_get_uint8(x_11, 8);
x_92 = lean_ctor_get_uint8(x_11, 9);
x_93 = lean_ctor_get_uint8(x_11, 11);
if (lean_is_exclusive(x_11)) {
 x_94 = x_11;
} else {
 lean_dec_ref(x_11);
 x_94 = lean_box(0);
}
x_95 = 1;
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 0, 12);
} else {
 x_96 = x_94;
}
lean_ctor_set_uint8(x_96, 0, x_83);
lean_ctor_set_uint8(x_96, 1, x_84);
lean_ctor_set_uint8(x_96, 2, x_85);
lean_ctor_set_uint8(x_96, 3, x_86);
lean_ctor_set_uint8(x_96, 4, x_87);
lean_ctor_set_uint8(x_96, 5, x_88);
lean_ctor_set_uint8(x_96, 6, x_89);
lean_ctor_set_uint8(x_96, 7, x_90);
lean_ctor_set_uint8(x_96, 8, x_91);
lean_ctor_set_uint8(x_96, 9, x_92);
lean_ctor_set_uint8(x_96, 10, x_95);
lean_ctor_set_uint8(x_96, 11, x_93);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_82);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_97);
x_98 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_97, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_97);
x_101 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_97, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Meta_Closure_process(x_3, x_4, x_97, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
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
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_102);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_102);
lean_dec(x_99);
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_115 = x_101;
} else {
 lean_dec_ref(x_101);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_117 = lean_ctor_get(x_98, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_98, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_119 = x_98;
} else {
 lean_dec_ref(x_98);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
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
uint8_t x_31; 
lean_inc(x_22);
x_31 = l_Lean_Environment_hasUnsafe(x_17, x_22);
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
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_17);
x_72 = 0;
x_73 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_73, 0, x_21);
lean_ctor_set(x_73, 1, x_22);
lean_ctor_set(x_73, 2, x_27);
lean_ctor_set(x_73, 3, x_30);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_74);
x_75 = l_Lean_addDecl(x_74, x_8, x_9, x_16);
if (lean_obj_tag(x_75) == 0)
{
if (x_5 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_77, x_6, x_7, x_8, x_9, x_76);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
lean_inc(x_9);
lean_inc(x_8);
x_80 = l_Lean_compileDecl(x_74, x_8, x_9, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_12, x_1, x_81, x_6, x_7, x_8, x_9, x_82);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_81);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_74);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
return x_75;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_11);
if (x_92 == 0)
{
return x_11;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_11, 0);
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_11);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_Lean_Environment_hasUnsafe(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
lean_inc(x_19);
x_20 = l_Lean_Environment_hasUnsafe(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_array_to_list(lean_box(0), x_21);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_17);
x_24 = lean_box(0);
lean_inc(x_1);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_addDecl(x_27, x_7, x_8, x_15);
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
x_32 = lean_array_to_list(lean_box(0), x_31);
x_33 = l_Lean_Expr_const___override(x_1, x_32);
x_34 = lean_ctor_get(x_11, 4);
lean_inc(x_34);
lean_dec(x_11);
x_35 = l_Lean_mkAppN(x_33, x_34);
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
x_38 = lean_array_to_list(lean_box(0), x_37);
x_39 = l_Lean_Expr_const___override(x_1, x_38);
x_40 = lean_ctor_get(x_11, 4);
lean_inc(x_40);
lean_dec(x_11);
x_41 = l_Lean_mkAppN(x_39, x_40);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
x_48 = lean_array_to_list(lean_box(0), x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_17);
x_50 = lean_box(0);
lean_inc(x_1);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = 0;
x_54 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_addDecl(x_55, x_7, x_8, x_15);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_11, 3);
lean_inc(x_59);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = l_Lean_Expr_const___override(x_1, x_60);
x_62 = lean_ctor_get(x_11, 4);
lean_inc(x_62);
lean_dec(x_11);
x_63 = l_Lean_mkAppN(x_61, x_62);
lean_ctor_set(x_56, 0, x_63);
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_ctor_get(x_11, 3);
lean_inc(x_65);
x_66 = lean_array_to_list(lean_box(0), x_65);
x_67 = l_Lean_Expr_const___override(x_1, x_66);
x_68 = lean_ctor_get(x_11, 4);
lean_inc(x_68);
lean_dec(x_11);
x_69 = l_Lean_mkAppN(x_67, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_56);
if (x_71 == 0)
{
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
x_76 = lean_array_to_list(lean_box(0), x_75);
lean_inc(x_1);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_17);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_78);
x_79 = lean_box(0);
lean_inc(x_1);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_addDecl(x_84, x_7, x_8, x_15);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_11, 3);
lean_inc(x_88);
x_89 = lean_array_to_list(lean_box(0), x_88);
x_90 = l_Lean_Expr_const___override(x_1, x_89);
x_91 = lean_ctor_get(x_11, 4);
lean_inc(x_91);
lean_dec(x_11);
x_92 = l_Lean_mkAppN(x_90, x_91);
lean_ctor_set(x_85, 0, x_92);
return x_85;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_dec(x_85);
x_94 = lean_ctor_get(x_11, 3);
lean_inc(x_94);
x_95 = lean_array_to_list(lean_box(0), x_94);
x_96 = l_Lean_Expr_const___override(x_1, x_95);
x_97 = lean_ctor_get(x_11, 4);
lean_inc(x_97);
lean_dec(x_11);
x_98 = l_Lean_mkAppN(x_96, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_11);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_10);
if (x_104 == 0)
{
return x_10;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_10, 0);
x_106 = lean_ctor_get(x_10, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_10);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
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
