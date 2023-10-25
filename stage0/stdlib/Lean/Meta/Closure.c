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
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_3 = lean_unsigned_to_nat(1518u);
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
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateApp!Impl", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("application expected", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__5;
x_3 = lean_unsigned_to_nat(1480u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateLambdaE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lambda expected", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__8;
x_3 = lean_unsigned_to_nat(1575u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateForallE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forall expected", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__11;
x_3 = lean_unsigned_to_nat(1555u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__12;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateLet!Impl", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let expression expected", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__14;
x_3 = lean_unsigned_to_nat(1584u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__15;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__17;
x_3 = lean_unsigned_to_nat(1529u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__18;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_FVarId_getValue_x3f(x_23, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
if (x_2 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_Closure_pushToProcess(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Expr_fvar___override(x_27);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Expr_fvar___override(x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Meta_Closure_pushToProcess(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lean_Expr_fvar___override(x_40);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lean_Expr_fvar___override(x_40);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_23);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_37, 0);
lean_inc(x_51);
lean_dec(x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Meta_Closure_preprocess(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_128; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_128 = l_Lean_Expr_hasLevelParam(x_54);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = l_Lean_Expr_hasFVar(x_54);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = l_Lean_Expr_hasMVar(x_54);
if (x_130 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_52;
}
else
{
lean_object* x_131; 
lean_free_object(x_52);
x_131 = lean_box(0);
x_56 = x_131;
goto block_127;
}
}
else
{
lean_object* x_132; 
lean_free_object(x_52);
x_132 = lean_box(0);
x_56 = x_132;
goto block_127;
}
}
else
{
lean_object* x_133; 
lean_free_object(x_52);
x_133 = lean_box(0);
x_56 = x_133;
goto block_127;
}
block_127:
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_56);
x_57 = lean_st_ref_get(x_3, x_55);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_54);
x_62 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_61, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_free_object(x_57);
lean_inc(x_54);
x_63 = l_Lean_Meta_Closure_collectExprAux(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_take(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_64);
x_71 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_70, x_54, x_64);
x_72 = lean_ctor_get(x_67, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 6);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 7);
lean_inc(x_77);
x_78 = lean_ctor_get(x_67, 8);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 9);
lean_inc(x_79);
x_80 = lean_ctor_get(x_67, 10);
lean_inc(x_80);
x_81 = lean_ctor_get(x_67, 11);
lean_inc(x_81);
lean_dec(x_67);
x_82 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set(x_82, 2, x_72);
lean_ctor_set(x_82, 3, x_73);
lean_ctor_set(x_82, 4, x_74);
lean_ctor_set(x_82, 5, x_75);
lean_ctor_set(x_82, 6, x_76);
lean_ctor_set(x_82, 7, x_77);
lean_ctor_set(x_82, 8, x_78);
lean_ctor_set(x_82, 9, x_79);
lean_ctor_set(x_82, 10, x_80);
lean_ctor_set(x_82, 11, x_81);
x_83 = lean_st_ref_set(x_3, x_82, x_68);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_64);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_64);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_54);
x_88 = !lean_is_exclusive(x_63);
if (x_88 == 0)
{
return x_63;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_63, 0);
x_90 = lean_ctor_get(x_63, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_63);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_92 = lean_ctor_get(x_62, 0);
lean_inc(x_92);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_92);
return x_57;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_57, 0);
x_94 = lean_ctor_get(x_57, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_57);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_54);
x_96 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_95, x_54);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_inc(x_54);
x_97 = l_Lean_Meta_Closure_collectExprAux(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_st_ref_take(x_3, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_98);
x_105 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_104, x_54, x_98);
x_106 = lean_ctor_get(x_101, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 7);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 8);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 9);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 10);
lean_inc(x_114);
x_115 = lean_ctor_get(x_101, 11);
lean_inc(x_115);
lean_dec(x_101);
x_116 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_116, 0, x_103);
lean_ctor_set(x_116, 1, x_105);
lean_ctor_set(x_116, 2, x_106);
lean_ctor_set(x_116, 3, x_107);
lean_ctor_set(x_116, 4, x_108);
lean_ctor_set(x_116, 5, x_109);
lean_ctor_set(x_116, 6, x_110);
lean_ctor_set(x_116, 7, x_111);
lean_ctor_set(x_116, 8, x_112);
lean_ctor_set(x_116, 9, x_113);
lean_ctor_set(x_116, 10, x_114);
lean_ctor_set(x_116, 11, x_115);
x_117 = lean_st_ref_set(x_3, x_116, x_102);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_98);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_54);
x_121 = lean_ctor_get(x_97, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_97, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_123 = x_97;
} else {
 lean_dec_ref(x_97);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_125 = lean_ctor_get(x_96, 0);
lean_inc(x_125);
lean_dec(x_96);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_94);
return x_126;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_174; 
x_134 = lean_ctor_get(x_52, 0);
x_135 = lean_ctor_get(x_52, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_52);
x_174 = l_Lean_Expr_hasLevelParam(x_134);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasFVar(x_134);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_hasMVar(x_134);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_134);
lean_ctor_set(x_177, 1, x_135);
return x_177;
}
else
{
lean_object* x_178; 
x_178 = lean_box(0);
x_136 = x_178;
goto block_173;
}
}
else
{
lean_object* x_179; 
x_179 = lean_box(0);
x_136 = x_179;
goto block_173;
}
}
else
{
lean_object* x_180; 
x_180 = lean_box(0);
x_136 = x_180;
goto block_173;
}
block_173:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_136);
x_137 = lean_st_ref_get(x_3, x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
lean_inc(x_134);
x_142 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_141, x_134);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec(x_140);
lean_inc(x_134);
x_143 = l_Lean_Meta_Closure_collectExprAux(x_134, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_st_ref_take(x_3, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_inc(x_144);
x_151 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_150, x_134, x_144);
x_152 = lean_ctor_get(x_147, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_147, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_147, 4);
lean_inc(x_154);
x_155 = lean_ctor_get(x_147, 5);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 6);
lean_inc(x_156);
x_157 = lean_ctor_get(x_147, 7);
lean_inc(x_157);
x_158 = lean_ctor_get(x_147, 8);
lean_inc(x_158);
x_159 = lean_ctor_get(x_147, 9);
lean_inc(x_159);
x_160 = lean_ctor_get(x_147, 10);
lean_inc(x_160);
x_161 = lean_ctor_get(x_147, 11);
lean_inc(x_161);
lean_dec(x_147);
x_162 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_151);
lean_ctor_set(x_162, 2, x_152);
lean_ctor_set(x_162, 3, x_153);
lean_ctor_set(x_162, 4, x_154);
lean_ctor_set(x_162, 5, x_155);
lean_ctor_set(x_162, 6, x_156);
lean_ctor_set(x_162, 7, x_157);
lean_ctor_set(x_162, 8, x_158);
lean_ctor_set(x_162, 9, x_159);
lean_ctor_set(x_162, 10, x_160);
lean_ctor_set(x_162, 11, x_161);
x_163 = lean_st_ref_set(x_3, x_162, x_148);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_144);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_134);
x_167 = lean_ctor_get(x_143, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_143, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_169 = x_143;
} else {
 lean_dec_ref(x_143);
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
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_171 = lean_ctor_get(x_142, 0);
lean_inc(x_171);
lean_dec(x_142);
if (lean_is_scalar(x_140)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_140;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_139);
return x_172;
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_181 = !lean_is_exclusive(x_52);
if (x_181 == 0)
{
return x_52;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_52, 0);
x_183 = lean_ctor_get(x_52, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_52);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_185 = !lean_is_exclusive(x_24);
if (x_185 == 0)
{
return x_24;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_24, 0);
x_187 = lean_ctor_get(x_24, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_24);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
case 2:
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
x_190 = l_Lean_MVarId_getDecl(x_189, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 2);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_194 = l_Lean_Meta_Closure_preprocess(x_193, x_2, x_3, x_4, x_5, x_6, x_7, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_235; uint8_t x_269; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_269 = l_Lean_Expr_hasLevelParam(x_195);
if (x_269 == 0)
{
uint8_t x_270; 
x_270 = l_Lean_Expr_hasFVar(x_195);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = l_Lean_Expr_hasMVar(x_195);
if (x_271 == 0)
{
x_197 = x_195;
x_198 = x_196;
goto block_234;
}
else
{
lean_object* x_272; 
x_272 = lean_box(0);
x_235 = x_272;
goto block_268;
}
}
else
{
lean_object* x_273; 
x_273 = lean_box(0);
x_235 = x_273;
goto block_268;
}
}
else
{
lean_object* x_274; 
x_274 = lean_box(0);
x_235 = x_274;
goto block_268;
}
block_234:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_199 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_201);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_st_ref_take(x_3, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 3);
lean_inc(x_211);
x_212 = lean_ctor_get(x_206, 4);
lean_inc(x_212);
x_213 = lean_ctor_get(x_206, 5);
lean_inc(x_213);
x_214 = lean_ctor_get(x_206, 6);
lean_inc(x_214);
x_215 = lean_unsigned_to_nat(0u);
x_216 = 0;
x_217 = 0;
lean_inc(x_200);
x_218 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_200);
lean_ctor_set(x_218, 2, x_203);
lean_ctor_set(x_218, 3, x_197);
lean_ctor_set_uint8(x_218, sizeof(void*)*4, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 1, x_217);
x_219 = lean_array_push(x_214, x_218);
x_220 = lean_ctor_get(x_206, 7);
lean_inc(x_220);
x_221 = lean_ctor_get(x_206, 8);
lean_inc(x_221);
x_222 = lean_ctor_get(x_206, 9);
lean_inc(x_222);
x_223 = lean_array_push(x_222, x_1);
x_224 = lean_ctor_get(x_206, 10);
lean_inc(x_224);
x_225 = lean_ctor_get(x_206, 11);
lean_inc(x_225);
lean_dec(x_206);
x_226 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_226, 0, x_208);
lean_ctor_set(x_226, 1, x_209);
lean_ctor_set(x_226, 2, x_210);
lean_ctor_set(x_226, 3, x_211);
lean_ctor_set(x_226, 4, x_212);
lean_ctor_set(x_226, 5, x_213);
lean_ctor_set(x_226, 6, x_219);
lean_ctor_set(x_226, 7, x_220);
lean_ctor_set(x_226, 8, x_221);
lean_ctor_set(x_226, 9, x_223);
lean_ctor_set(x_226, 10, x_224);
lean_ctor_set(x_226, 11, x_225);
x_227 = lean_st_ref_set(x_3, x_226, x_207);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
lean_dec(x_229);
x_230 = l_Lean_Expr_fvar___override(x_200);
lean_ctor_set(x_227, 0, x_230);
return x_227;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_dec(x_227);
x_232 = l_Lean_Expr_fvar___override(x_200);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
block_268:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_235);
x_236 = lean_st_ref_get(x_3, x_196);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_195);
x_240 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_239, x_195);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_195);
x_241 = l_Lean_Meta_Closure_collectExprAux(x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_238);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_st_ref_take(x_3, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_inc(x_242);
x_249 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_248, x_195, x_242);
x_250 = lean_ctor_get(x_245, 2);
lean_inc(x_250);
x_251 = lean_ctor_get(x_245, 3);
lean_inc(x_251);
x_252 = lean_ctor_get(x_245, 4);
lean_inc(x_252);
x_253 = lean_ctor_get(x_245, 5);
lean_inc(x_253);
x_254 = lean_ctor_get(x_245, 6);
lean_inc(x_254);
x_255 = lean_ctor_get(x_245, 7);
lean_inc(x_255);
x_256 = lean_ctor_get(x_245, 8);
lean_inc(x_256);
x_257 = lean_ctor_get(x_245, 9);
lean_inc(x_257);
x_258 = lean_ctor_get(x_245, 10);
lean_inc(x_258);
x_259 = lean_ctor_get(x_245, 11);
lean_inc(x_259);
lean_dec(x_245);
x_260 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_260, 0, x_247);
lean_ctor_set(x_260, 1, x_249);
lean_ctor_set(x_260, 2, x_250);
lean_ctor_set(x_260, 3, x_251);
lean_ctor_set(x_260, 4, x_252);
lean_ctor_set(x_260, 5, x_253);
lean_ctor_set(x_260, 6, x_254);
lean_ctor_set(x_260, 7, x_255);
lean_ctor_set(x_260, 8, x_256);
lean_ctor_set(x_260, 9, x_257);
lean_ctor_set(x_260, 10, x_258);
lean_ctor_set(x_260, 11, x_259);
x_261 = lean_st_ref_set(x_3, x_260, x_246);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_197 = x_242;
x_198 = x_262;
goto block_234;
}
else
{
uint8_t x_263; 
lean_dec(x_195);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_241);
if (x_263 == 0)
{
return x_241;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_241, 0);
x_265 = lean_ctor_get(x_241, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_241);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; 
lean_dec(x_195);
x_267 = lean_ctor_get(x_240, 0);
lean_inc(x_267);
lean_dec(x_240);
x_197 = x_267;
x_198 = x_238;
goto block_234;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_194);
if (x_275 == 0)
{
return x_194;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_194, 0);
x_277 = lean_ctor_get(x_194, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_194);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_190);
if (x_279 == 0)
{
return x_190;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_190, 0);
x_281 = lean_ctor_get(x_190, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_190);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
case 3:
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_1, 0);
lean_inc(x_283);
lean_inc(x_283);
x_284 = l_Lean_Meta_Closure_collectLevel(x_283, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; size_t x_287; size_t x_288; uint8_t x_289; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = lean_ptr_addr(x_283);
lean_dec(x_283);
x_288 = lean_ptr_addr(x_286);
x_289 = lean_usize_dec_eq(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_1);
x_290 = l_Lean_Expr_sort___override(x_286);
lean_ctor_set(x_284, 0, x_290);
return x_284;
}
else
{
lean_dec(x_286);
lean_ctor_set(x_284, 0, x_1);
return x_284;
}
}
else
{
lean_object* x_291; lean_object* x_292; size_t x_293; size_t x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_284, 0);
x_292 = lean_ctor_get(x_284, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_284);
x_293 = lean_ptr_addr(x_283);
lean_dec(x_283);
x_294 = lean_ptr_addr(x_291);
x_295 = lean_usize_dec_eq(x_293, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_1);
x_296 = l_Lean_Expr_sort___override(x_291);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_292);
return x_297;
}
else
{
lean_object* x_298; 
lean_dec(x_291);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_1);
lean_ctor_set(x_298, 1, x_292);
return x_298;
}
}
}
case 4:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_299 = lean_ctor_get(x_1, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_1, 1);
lean_inc(x_300);
x_301 = lean_box(0);
lean_inc(x_300);
x_302 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_300, x_301, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_ctor_get(x_302, 0);
x_305 = l_ptrEqList___rarg(x_300, x_304);
lean_dec(x_300);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec(x_1);
x_306 = l_Lean_Expr_const___override(x_299, x_304);
lean_ctor_set(x_302, 0, x_306);
return x_302;
}
else
{
lean_dec(x_304);
lean_dec(x_299);
lean_ctor_set(x_302, 0, x_1);
return x_302;
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_302, 0);
x_308 = lean_ctor_get(x_302, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_302);
x_309 = l_ptrEqList___rarg(x_300, x_307);
lean_dec(x_300);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_1);
x_310 = l_Lean_Expr_const___override(x_299, x_307);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
else
{
lean_object* x_312; 
lean_dec(x_307);
lean_dec(x_299);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_308);
return x_312;
}
}
}
case 5:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_377; uint8_t x_411; 
x_313 = lean_ctor_get(x_1, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_1, 1);
lean_inc(x_314);
x_411 = l_Lean_Expr_hasLevelParam(x_313);
if (x_411 == 0)
{
uint8_t x_412; 
x_412 = l_Lean_Expr_hasFVar(x_313);
if (x_412 == 0)
{
uint8_t x_413; 
x_413 = l_Lean_Expr_hasMVar(x_313);
if (x_413 == 0)
{
x_315 = x_313;
x_316 = x_8;
goto block_376;
}
else
{
lean_object* x_414; 
x_414 = lean_box(0);
x_377 = x_414;
goto block_410;
}
}
else
{
lean_object* x_415; 
x_415 = lean_box(0);
x_377 = x_415;
goto block_410;
}
}
else
{
lean_object* x_416; 
x_416 = lean_box(0);
x_377 = x_416;
goto block_410;
}
block_376:
{
lean_object* x_317; lean_object* x_318; lean_object* x_336; uint8_t x_370; 
x_370 = l_Lean_Expr_hasLevelParam(x_314);
if (x_370 == 0)
{
uint8_t x_371; 
x_371 = l_Lean_Expr_hasFVar(x_314);
if (x_371 == 0)
{
uint8_t x_372; 
x_372 = l_Lean_Expr_hasMVar(x_314);
if (x_372 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_317 = x_314;
x_318 = x_316;
goto block_335;
}
else
{
lean_object* x_373; 
x_373 = lean_box(0);
x_336 = x_373;
goto block_369;
}
}
else
{
lean_object* x_374; 
x_374 = lean_box(0);
x_336 = x_374;
goto block_369;
}
}
else
{
lean_object* x_375; 
x_375 = lean_box(0);
x_336 = x_375;
goto block_369;
}
block_335:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_319; lean_object* x_320; size_t x_321; size_t x_322; uint8_t x_323; 
x_319 = lean_ctor_get(x_1, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_1, 1);
lean_inc(x_320);
x_321 = lean_ptr_addr(x_319);
lean_dec(x_319);
x_322 = lean_ptr_addr(x_315);
x_323 = lean_usize_dec_eq(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_320);
lean_dec(x_1);
x_324 = l_Lean_Expr_app___override(x_315, x_317);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_318);
return x_325;
}
else
{
size_t x_326; size_t x_327; uint8_t x_328; 
x_326 = lean_ptr_addr(x_320);
lean_dec(x_320);
x_327 = lean_ptr_addr(x_317);
x_328 = lean_usize_dec_eq(x_326, x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_1);
x_329 = l_Lean_Expr_app___override(x_315, x_317);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_318);
return x_330;
}
else
{
lean_object* x_331; 
lean_dec(x_317);
lean_dec(x_315);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_1);
lean_ctor_set(x_331, 1, x_318);
return x_331;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_1);
x_332 = l_Lean_Meta_Closure_collectExprAux___closed__7;
x_333 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_318);
return x_334;
}
}
block_369:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_336);
x_337 = lean_st_ref_get(x_3, x_316);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
lean_inc(x_314);
x_341 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_340, x_314);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
lean_inc(x_314);
x_342 = l_Lean_Meta_Closure_collectExprAux(x_314, x_2, x_3, x_4, x_5, x_6, x_7, x_339);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_st_ref_take(x_3, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_inc(x_343);
x_350 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_349, x_314, x_343);
x_351 = lean_ctor_get(x_346, 2);
lean_inc(x_351);
x_352 = lean_ctor_get(x_346, 3);
lean_inc(x_352);
x_353 = lean_ctor_get(x_346, 4);
lean_inc(x_353);
x_354 = lean_ctor_get(x_346, 5);
lean_inc(x_354);
x_355 = lean_ctor_get(x_346, 6);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 7);
lean_inc(x_356);
x_357 = lean_ctor_get(x_346, 8);
lean_inc(x_357);
x_358 = lean_ctor_get(x_346, 9);
lean_inc(x_358);
x_359 = lean_ctor_get(x_346, 10);
lean_inc(x_359);
x_360 = lean_ctor_get(x_346, 11);
lean_inc(x_360);
lean_dec(x_346);
x_361 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_361, 0, x_348);
lean_ctor_set(x_361, 1, x_350);
lean_ctor_set(x_361, 2, x_351);
lean_ctor_set(x_361, 3, x_352);
lean_ctor_set(x_361, 4, x_353);
lean_ctor_set(x_361, 5, x_354);
lean_ctor_set(x_361, 6, x_355);
lean_ctor_set(x_361, 7, x_356);
lean_ctor_set(x_361, 8, x_357);
lean_ctor_set(x_361, 9, x_358);
lean_ctor_set(x_361, 10, x_359);
lean_ctor_set(x_361, 11, x_360);
x_362 = lean_st_ref_set(x_3, x_361, x_347);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_317 = x_343;
x_318 = x_363;
goto block_335;
}
else
{
uint8_t x_364; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_1);
x_364 = !lean_is_exclusive(x_342);
if (x_364 == 0)
{
return x_342;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_342, 0);
x_366 = lean_ctor_get(x_342, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_342);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
else
{
lean_object* x_368; 
lean_dec(x_314);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_368 = lean_ctor_get(x_341, 0);
lean_inc(x_368);
lean_dec(x_341);
x_317 = x_368;
x_318 = x_339;
goto block_335;
}
}
}
block_410:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
x_378 = lean_st_ref_get(x_3, x_8);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_313);
x_382 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_381, x_313);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_313);
x_383 = l_Lean_Meta_Closure_collectExprAux(x_313, x_2, x_3, x_4, x_5, x_6, x_7, x_380);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = lean_st_ref_take(x_3, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_inc(x_384);
x_391 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_390, x_313, x_384);
x_392 = lean_ctor_get(x_387, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_387, 3);
lean_inc(x_393);
x_394 = lean_ctor_get(x_387, 4);
lean_inc(x_394);
x_395 = lean_ctor_get(x_387, 5);
lean_inc(x_395);
x_396 = lean_ctor_get(x_387, 6);
lean_inc(x_396);
x_397 = lean_ctor_get(x_387, 7);
lean_inc(x_397);
x_398 = lean_ctor_get(x_387, 8);
lean_inc(x_398);
x_399 = lean_ctor_get(x_387, 9);
lean_inc(x_399);
x_400 = lean_ctor_get(x_387, 10);
lean_inc(x_400);
x_401 = lean_ctor_get(x_387, 11);
lean_inc(x_401);
lean_dec(x_387);
x_402 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_402, 0, x_389);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_393);
lean_ctor_set(x_402, 4, x_394);
lean_ctor_set(x_402, 5, x_395);
lean_ctor_set(x_402, 6, x_396);
lean_ctor_set(x_402, 7, x_397);
lean_ctor_set(x_402, 8, x_398);
lean_ctor_set(x_402, 9, x_399);
lean_ctor_set(x_402, 10, x_400);
lean_ctor_set(x_402, 11, x_401);
x_403 = lean_st_ref_set(x_3, x_402, x_388);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_315 = x_384;
x_316 = x_404;
goto block_376;
}
else
{
uint8_t x_405; 
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_383);
if (x_405 == 0)
{
return x_383;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_383, 0);
x_407 = lean_ctor_get(x_383, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_383);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
lean_object* x_409; 
lean_dec(x_313);
x_409 = lean_ctor_get(x_382, 0);
lean_inc(x_409);
lean_dec(x_382);
x_315 = x_409;
x_316 = x_380;
goto block_376;
}
}
}
case 6:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_487; uint8_t x_521; 
x_417 = lean_ctor_get(x_1, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_1, 2);
lean_inc(x_418);
x_521 = l_Lean_Expr_hasLevelParam(x_417);
if (x_521 == 0)
{
uint8_t x_522; 
x_522 = l_Lean_Expr_hasFVar(x_417);
if (x_522 == 0)
{
uint8_t x_523; 
x_523 = l_Lean_Expr_hasMVar(x_417);
if (x_523 == 0)
{
x_419 = x_417;
x_420 = x_8;
goto block_486;
}
else
{
lean_object* x_524; 
x_524 = lean_box(0);
x_487 = x_524;
goto block_520;
}
}
else
{
lean_object* x_525; 
x_525 = lean_box(0);
x_487 = x_525;
goto block_520;
}
}
else
{
lean_object* x_526; 
x_526 = lean_box(0);
x_487 = x_526;
goto block_520;
}
block_486:
{
lean_object* x_421; lean_object* x_422; lean_object* x_446; uint8_t x_480; 
x_480 = l_Lean_Expr_hasLevelParam(x_418);
if (x_480 == 0)
{
uint8_t x_481; 
x_481 = l_Lean_Expr_hasFVar(x_418);
if (x_481 == 0)
{
uint8_t x_482; 
x_482 = l_Lean_Expr_hasMVar(x_418);
if (x_482 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_421 = x_418;
x_422 = x_420;
goto block_445;
}
else
{
lean_object* x_483; 
x_483 = lean_box(0);
x_446 = x_483;
goto block_479;
}
}
else
{
lean_object* x_484; 
x_484 = lean_box(0);
x_446 = x_484;
goto block_479;
}
}
else
{
lean_object* x_485; 
x_485 = lean_box(0);
x_446 = x_485;
goto block_479;
}
block_445:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; size_t x_428; size_t x_429; uint8_t x_430; 
x_423 = lean_ctor_get(x_1, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_1, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 2);
lean_inc(x_425);
x_426 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
x_427 = l_Lean_Expr_lam___override(x_423, x_424, x_425, x_426);
x_428 = lean_ptr_addr(x_424);
lean_dec(x_424);
x_429 = lean_ptr_addr(x_419);
x_430 = lean_usize_dec_eq(x_428, x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_427);
lean_dec(x_425);
x_431 = l_Lean_Expr_lam___override(x_423, x_419, x_421, x_426);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_422);
return x_432;
}
else
{
size_t x_433; size_t x_434; uint8_t x_435; 
x_433 = lean_ptr_addr(x_425);
lean_dec(x_425);
x_434 = lean_ptr_addr(x_421);
x_435 = lean_usize_dec_eq(x_433, x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_427);
x_436 = l_Lean_Expr_lam___override(x_423, x_419, x_421, x_426);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_422);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_426, x_426);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
lean_dec(x_427);
x_439 = l_Lean_Expr_lam___override(x_423, x_419, x_421, x_426);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_422);
return x_440;
}
else
{
lean_object* x_441; 
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_419);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_427);
lean_ctor_set(x_441, 1, x_422);
return x_441;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_1);
x_442 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_443 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_442);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_422);
return x_444;
}
}
block_479:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_446);
x_447 = lean_st_ref_get(x_3, x_420);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_418);
x_451 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_450, x_418);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
lean_inc(x_418);
x_452 = l_Lean_Meta_Closure_collectExprAux(x_418, x_2, x_3, x_4, x_5, x_6, x_7, x_449);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_st_ref_take(x_3, x_454);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_ctor_get(x_456, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_inc(x_453);
x_460 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_459, x_418, x_453);
x_461 = lean_ctor_get(x_456, 2);
lean_inc(x_461);
x_462 = lean_ctor_get(x_456, 3);
lean_inc(x_462);
x_463 = lean_ctor_get(x_456, 4);
lean_inc(x_463);
x_464 = lean_ctor_get(x_456, 5);
lean_inc(x_464);
x_465 = lean_ctor_get(x_456, 6);
lean_inc(x_465);
x_466 = lean_ctor_get(x_456, 7);
lean_inc(x_466);
x_467 = lean_ctor_get(x_456, 8);
lean_inc(x_467);
x_468 = lean_ctor_get(x_456, 9);
lean_inc(x_468);
x_469 = lean_ctor_get(x_456, 10);
lean_inc(x_469);
x_470 = lean_ctor_get(x_456, 11);
lean_inc(x_470);
lean_dec(x_456);
x_471 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_471, 0, x_458);
lean_ctor_set(x_471, 1, x_460);
lean_ctor_set(x_471, 2, x_461);
lean_ctor_set(x_471, 3, x_462);
lean_ctor_set(x_471, 4, x_463);
lean_ctor_set(x_471, 5, x_464);
lean_ctor_set(x_471, 6, x_465);
lean_ctor_set(x_471, 7, x_466);
lean_ctor_set(x_471, 8, x_467);
lean_ctor_set(x_471, 9, x_468);
lean_ctor_set(x_471, 10, x_469);
lean_ctor_set(x_471, 11, x_470);
x_472 = lean_st_ref_set(x_3, x_471, x_457);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_421 = x_453;
x_422 = x_473;
goto block_445;
}
else
{
uint8_t x_474; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_1);
x_474 = !lean_is_exclusive(x_452);
if (x_474 == 0)
{
return x_452;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_452, 0);
x_476 = lean_ctor_get(x_452, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_452);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
lean_object* x_478; 
lean_dec(x_418);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_478 = lean_ctor_get(x_451, 0);
lean_inc(x_478);
lean_dec(x_451);
x_421 = x_478;
x_422 = x_449;
goto block_445;
}
}
}
block_520:
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_487);
x_488 = lean_st_ref_get(x_3, x_8);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
lean_inc(x_417);
x_492 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_491, x_417);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_417);
x_493 = l_Lean_Meta_Closure_collectExprAux(x_417, x_2, x_3, x_4, x_5, x_6, x_7, x_490);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_st_ref_take(x_3, x_495);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_inc(x_494);
x_501 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_500, x_417, x_494);
x_502 = lean_ctor_get(x_497, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_497, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_497, 4);
lean_inc(x_504);
x_505 = lean_ctor_get(x_497, 5);
lean_inc(x_505);
x_506 = lean_ctor_get(x_497, 6);
lean_inc(x_506);
x_507 = lean_ctor_get(x_497, 7);
lean_inc(x_507);
x_508 = lean_ctor_get(x_497, 8);
lean_inc(x_508);
x_509 = lean_ctor_get(x_497, 9);
lean_inc(x_509);
x_510 = lean_ctor_get(x_497, 10);
lean_inc(x_510);
x_511 = lean_ctor_get(x_497, 11);
lean_inc(x_511);
lean_dec(x_497);
x_512 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_512, 0, x_499);
lean_ctor_set(x_512, 1, x_501);
lean_ctor_set(x_512, 2, x_502);
lean_ctor_set(x_512, 3, x_503);
lean_ctor_set(x_512, 4, x_504);
lean_ctor_set(x_512, 5, x_505);
lean_ctor_set(x_512, 6, x_506);
lean_ctor_set(x_512, 7, x_507);
lean_ctor_set(x_512, 8, x_508);
lean_ctor_set(x_512, 9, x_509);
lean_ctor_set(x_512, 10, x_510);
lean_ctor_set(x_512, 11, x_511);
x_513 = lean_st_ref_set(x_3, x_512, x_498);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_419 = x_494;
x_420 = x_514;
goto block_486;
}
else
{
uint8_t x_515; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_493);
if (x_515 == 0)
{
return x_493;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_493, 0);
x_517 = lean_ctor_get(x_493, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_493);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
else
{
lean_object* x_519; 
lean_dec(x_417);
x_519 = lean_ctor_get(x_492, 0);
lean_inc(x_519);
lean_dec(x_492);
x_419 = x_519;
x_420 = x_490;
goto block_486;
}
}
}
case 7:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_597; uint8_t x_631; 
x_527 = lean_ctor_get(x_1, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_1, 2);
lean_inc(x_528);
x_631 = l_Lean_Expr_hasLevelParam(x_527);
if (x_631 == 0)
{
uint8_t x_632; 
x_632 = l_Lean_Expr_hasFVar(x_527);
if (x_632 == 0)
{
uint8_t x_633; 
x_633 = l_Lean_Expr_hasMVar(x_527);
if (x_633 == 0)
{
x_529 = x_527;
x_530 = x_8;
goto block_596;
}
else
{
lean_object* x_634; 
x_634 = lean_box(0);
x_597 = x_634;
goto block_630;
}
}
else
{
lean_object* x_635; 
x_635 = lean_box(0);
x_597 = x_635;
goto block_630;
}
}
else
{
lean_object* x_636; 
x_636 = lean_box(0);
x_597 = x_636;
goto block_630;
}
block_596:
{
lean_object* x_531; lean_object* x_532; lean_object* x_556; uint8_t x_590; 
x_590 = l_Lean_Expr_hasLevelParam(x_528);
if (x_590 == 0)
{
uint8_t x_591; 
x_591 = l_Lean_Expr_hasFVar(x_528);
if (x_591 == 0)
{
uint8_t x_592; 
x_592 = l_Lean_Expr_hasMVar(x_528);
if (x_592 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_531 = x_528;
x_532 = x_530;
goto block_555;
}
else
{
lean_object* x_593; 
x_593 = lean_box(0);
x_556 = x_593;
goto block_589;
}
}
else
{
lean_object* x_594; 
x_594 = lean_box(0);
x_556 = x_594;
goto block_589;
}
}
else
{
lean_object* x_595; 
x_595 = lean_box(0);
x_556 = x_595;
goto block_589;
}
block_555:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; size_t x_538; size_t x_539; uint8_t x_540; 
x_533 = lean_ctor_get(x_1, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_1, 1);
lean_inc(x_534);
x_535 = lean_ctor_get(x_1, 2);
lean_inc(x_535);
x_536 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
x_537 = l_Lean_Expr_forallE___override(x_533, x_534, x_535, x_536);
x_538 = lean_ptr_addr(x_534);
lean_dec(x_534);
x_539 = lean_ptr_addr(x_529);
x_540 = lean_usize_dec_eq(x_538, x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_537);
lean_dec(x_535);
x_541 = l_Lean_Expr_forallE___override(x_533, x_529, x_531, x_536);
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_532);
return x_542;
}
else
{
size_t x_543; size_t x_544; uint8_t x_545; 
x_543 = lean_ptr_addr(x_535);
lean_dec(x_535);
x_544 = lean_ptr_addr(x_531);
x_545 = lean_usize_dec_eq(x_543, x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_537);
x_546 = l_Lean_Expr_forallE___override(x_533, x_529, x_531, x_536);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_532);
return x_547;
}
else
{
uint8_t x_548; 
x_548 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_536, x_536);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_537);
x_549 = l_Lean_Expr_forallE___override(x_533, x_529, x_531, x_536);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_532);
return x_550;
}
else
{
lean_object* x_551; 
lean_dec(x_533);
lean_dec(x_531);
lean_dec(x_529);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_537);
lean_ctor_set(x_551, 1, x_532);
return x_551;
}
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_1);
x_552 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_553 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_552);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_532);
return x_554;
}
}
block_589:
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_556);
x_557 = lean_st_ref_get(x_3, x_530);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
lean_inc(x_528);
x_561 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_560, x_528);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; 
lean_inc(x_528);
x_562 = l_Lean_Meta_Closure_collectExprAux(x_528, x_2, x_3, x_4, x_5, x_6, x_7, x_559);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec(x_562);
x_565 = lean_st_ref_take(x_3, x_564);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
x_568 = lean_ctor_get(x_566, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_566, 1);
lean_inc(x_569);
lean_inc(x_563);
x_570 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_569, x_528, x_563);
x_571 = lean_ctor_get(x_566, 2);
lean_inc(x_571);
x_572 = lean_ctor_get(x_566, 3);
lean_inc(x_572);
x_573 = lean_ctor_get(x_566, 4);
lean_inc(x_573);
x_574 = lean_ctor_get(x_566, 5);
lean_inc(x_574);
x_575 = lean_ctor_get(x_566, 6);
lean_inc(x_575);
x_576 = lean_ctor_get(x_566, 7);
lean_inc(x_576);
x_577 = lean_ctor_get(x_566, 8);
lean_inc(x_577);
x_578 = lean_ctor_get(x_566, 9);
lean_inc(x_578);
x_579 = lean_ctor_get(x_566, 10);
lean_inc(x_579);
x_580 = lean_ctor_get(x_566, 11);
lean_inc(x_580);
lean_dec(x_566);
x_581 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_581, 0, x_568);
lean_ctor_set(x_581, 1, x_570);
lean_ctor_set(x_581, 2, x_571);
lean_ctor_set(x_581, 3, x_572);
lean_ctor_set(x_581, 4, x_573);
lean_ctor_set(x_581, 5, x_574);
lean_ctor_set(x_581, 6, x_575);
lean_ctor_set(x_581, 7, x_576);
lean_ctor_set(x_581, 8, x_577);
lean_ctor_set(x_581, 9, x_578);
lean_ctor_set(x_581, 10, x_579);
lean_ctor_set(x_581, 11, x_580);
x_582 = lean_st_ref_set(x_3, x_581, x_567);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
x_531 = x_563;
x_532 = x_583;
goto block_555;
}
else
{
uint8_t x_584; 
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_562);
if (x_584 == 0)
{
return x_562;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_562, 0);
x_586 = lean_ctor_get(x_562, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_562);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
else
{
lean_object* x_588; 
lean_dec(x_528);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_588 = lean_ctor_get(x_561, 0);
lean_inc(x_588);
lean_dec(x_561);
x_531 = x_588;
x_532 = x_559;
goto block_555;
}
}
}
block_630:
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_597);
x_598 = lean_st_ref_get(x_3, x_8);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
lean_inc(x_527);
x_602 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_601, x_527);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_527);
x_603 = l_Lean_Meta_Closure_collectExprAux(x_527, x_2, x_3, x_4, x_5, x_6, x_7, x_600);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_st_ref_take(x_3, x_605);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_ctor_get(x_607, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_inc(x_604);
x_611 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_610, x_527, x_604);
x_612 = lean_ctor_get(x_607, 2);
lean_inc(x_612);
x_613 = lean_ctor_get(x_607, 3);
lean_inc(x_613);
x_614 = lean_ctor_get(x_607, 4);
lean_inc(x_614);
x_615 = lean_ctor_get(x_607, 5);
lean_inc(x_615);
x_616 = lean_ctor_get(x_607, 6);
lean_inc(x_616);
x_617 = lean_ctor_get(x_607, 7);
lean_inc(x_617);
x_618 = lean_ctor_get(x_607, 8);
lean_inc(x_618);
x_619 = lean_ctor_get(x_607, 9);
lean_inc(x_619);
x_620 = lean_ctor_get(x_607, 10);
lean_inc(x_620);
x_621 = lean_ctor_get(x_607, 11);
lean_inc(x_621);
lean_dec(x_607);
x_622 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_622, 0, x_609);
lean_ctor_set(x_622, 1, x_611);
lean_ctor_set(x_622, 2, x_612);
lean_ctor_set(x_622, 3, x_613);
lean_ctor_set(x_622, 4, x_614);
lean_ctor_set(x_622, 5, x_615);
lean_ctor_set(x_622, 6, x_616);
lean_ctor_set(x_622, 7, x_617);
lean_ctor_set(x_622, 8, x_618);
lean_ctor_set(x_622, 9, x_619);
lean_ctor_set(x_622, 10, x_620);
lean_ctor_set(x_622, 11, x_621);
x_623 = lean_st_ref_set(x_3, x_622, x_608);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
lean_dec(x_623);
x_529 = x_604;
x_530 = x_624;
goto block_596;
}
else
{
uint8_t x_625; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_625 = !lean_is_exclusive(x_603);
if (x_625 == 0)
{
return x_603;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_603, 0);
x_627 = lean_ctor_get(x_603, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_603);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
else
{
lean_object* x_629; 
lean_dec(x_527);
x_629 = lean_ctor_get(x_602, 0);
lean_inc(x_629);
lean_dec(x_602);
x_529 = x_629;
x_530 = x_600;
goto block_596;
}
}
}
case 8:
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_753; uint8_t x_787; 
x_637 = lean_ctor_get(x_1, 1);
lean_inc(x_637);
x_638 = lean_ctor_get(x_1, 2);
lean_inc(x_638);
x_639 = lean_ctor_get(x_1, 3);
lean_inc(x_639);
x_787 = l_Lean_Expr_hasLevelParam(x_637);
if (x_787 == 0)
{
uint8_t x_788; 
x_788 = l_Lean_Expr_hasFVar(x_637);
if (x_788 == 0)
{
uint8_t x_789; 
x_789 = l_Lean_Expr_hasMVar(x_637);
if (x_789 == 0)
{
x_640 = x_637;
x_641 = x_8;
goto block_752;
}
else
{
lean_object* x_790; 
x_790 = lean_box(0);
x_753 = x_790;
goto block_786;
}
}
else
{
lean_object* x_791; 
x_791 = lean_box(0);
x_753 = x_791;
goto block_786;
}
}
else
{
lean_object* x_792; 
x_792 = lean_box(0);
x_753 = x_792;
goto block_786;
}
block_752:
{
lean_object* x_642; lean_object* x_643; lean_object* x_712; uint8_t x_746; 
x_746 = l_Lean_Expr_hasLevelParam(x_638);
if (x_746 == 0)
{
uint8_t x_747; 
x_747 = l_Lean_Expr_hasFVar(x_638);
if (x_747 == 0)
{
uint8_t x_748; 
x_748 = l_Lean_Expr_hasMVar(x_638);
if (x_748 == 0)
{
x_642 = x_638;
x_643 = x_641;
goto block_711;
}
else
{
lean_object* x_749; 
x_749 = lean_box(0);
x_712 = x_749;
goto block_745;
}
}
else
{
lean_object* x_750; 
x_750 = lean_box(0);
x_712 = x_750;
goto block_745;
}
}
else
{
lean_object* x_751; 
x_751 = lean_box(0);
x_712 = x_751;
goto block_745;
}
block_711:
{
lean_object* x_644; lean_object* x_645; lean_object* x_671; uint8_t x_705; 
x_705 = l_Lean_Expr_hasLevelParam(x_639);
if (x_705 == 0)
{
uint8_t x_706; 
x_706 = l_Lean_Expr_hasFVar(x_639);
if (x_706 == 0)
{
uint8_t x_707; 
x_707 = l_Lean_Expr_hasMVar(x_639);
if (x_707 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_644 = x_639;
x_645 = x_643;
goto block_670;
}
else
{
lean_object* x_708; 
x_708 = lean_box(0);
x_671 = x_708;
goto block_704;
}
}
else
{
lean_object* x_709; 
x_709 = lean_box(0);
x_671 = x_709;
goto block_704;
}
}
else
{
lean_object* x_710; 
x_710 = lean_box(0);
x_671 = x_710;
goto block_704;
}
block_670:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; size_t x_651; size_t x_652; uint8_t x_653; 
x_646 = lean_ctor_get(x_1, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_1, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_1, 2);
lean_inc(x_648);
x_649 = lean_ctor_get(x_1, 3);
lean_inc(x_649);
x_650 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_651 = lean_ptr_addr(x_647);
lean_dec(x_647);
x_652 = lean_ptr_addr(x_640);
x_653 = lean_usize_dec_eq(x_651, x_652);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; 
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_1);
x_654 = l_Lean_Expr_letE___override(x_646, x_640, x_642, x_644, x_650);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_645);
return x_655;
}
else
{
size_t x_656; size_t x_657; uint8_t x_658; 
x_656 = lean_ptr_addr(x_648);
lean_dec(x_648);
x_657 = lean_ptr_addr(x_642);
x_658 = lean_usize_dec_eq(x_656, x_657);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; 
lean_dec(x_649);
lean_dec(x_1);
x_659 = l_Lean_Expr_letE___override(x_646, x_640, x_642, x_644, x_650);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_645);
return x_660;
}
else
{
size_t x_661; size_t x_662; uint8_t x_663; 
x_661 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_662 = lean_ptr_addr(x_644);
x_663 = lean_usize_dec_eq(x_661, x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_1);
x_664 = l_Lean_Expr_letE___override(x_646, x_640, x_642, x_644, x_650);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_645);
return x_665;
}
else
{
lean_object* x_666; 
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_640);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_1);
lean_ctor_set(x_666, 1, x_645);
return x_666;
}
}
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_640);
lean_dec(x_1);
x_667 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_668 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_667);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_645);
return x_669;
}
}
block_704:
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_671);
x_672 = lean_st_ref_get(x_3, x_643);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
lean_inc(x_639);
x_676 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_675, x_639);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; 
lean_inc(x_639);
x_677 = l_Lean_Meta_Closure_collectExprAux(x_639, x_2, x_3, x_4, x_5, x_6, x_7, x_674);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = lean_st_ref_take(x_3, x_679);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_ctor_get(x_681, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_681, 1);
lean_inc(x_684);
lean_inc(x_678);
x_685 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_684, x_639, x_678);
x_686 = lean_ctor_get(x_681, 2);
lean_inc(x_686);
x_687 = lean_ctor_get(x_681, 3);
lean_inc(x_687);
x_688 = lean_ctor_get(x_681, 4);
lean_inc(x_688);
x_689 = lean_ctor_get(x_681, 5);
lean_inc(x_689);
x_690 = lean_ctor_get(x_681, 6);
lean_inc(x_690);
x_691 = lean_ctor_get(x_681, 7);
lean_inc(x_691);
x_692 = lean_ctor_get(x_681, 8);
lean_inc(x_692);
x_693 = lean_ctor_get(x_681, 9);
lean_inc(x_693);
x_694 = lean_ctor_get(x_681, 10);
lean_inc(x_694);
x_695 = lean_ctor_get(x_681, 11);
lean_inc(x_695);
lean_dec(x_681);
x_696 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_696, 0, x_683);
lean_ctor_set(x_696, 1, x_685);
lean_ctor_set(x_696, 2, x_686);
lean_ctor_set(x_696, 3, x_687);
lean_ctor_set(x_696, 4, x_688);
lean_ctor_set(x_696, 5, x_689);
lean_ctor_set(x_696, 6, x_690);
lean_ctor_set(x_696, 7, x_691);
lean_ctor_set(x_696, 8, x_692);
lean_ctor_set(x_696, 9, x_693);
lean_ctor_set(x_696, 10, x_694);
lean_ctor_set(x_696, 11, x_695);
x_697 = lean_st_ref_set(x_3, x_696, x_682);
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec(x_697);
x_644 = x_678;
x_645 = x_698;
goto block_670;
}
else
{
uint8_t x_699; 
lean_dec(x_642);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_1);
x_699 = !lean_is_exclusive(x_677);
if (x_699 == 0)
{
return x_677;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_677, 0);
x_701 = lean_ctor_get(x_677, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_677);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
}
else
{
lean_object* x_703; 
lean_dec(x_639);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_703 = lean_ctor_get(x_676, 0);
lean_inc(x_703);
lean_dec(x_676);
x_644 = x_703;
x_645 = x_674;
goto block_670;
}
}
}
block_745:
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_712);
x_713 = lean_st_ref_get(x_3, x_641);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
lean_inc(x_638);
x_717 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_716, x_638);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_638);
x_718 = l_Lean_Meta_Closure_collectExprAux(x_638, x_2, x_3, x_4, x_5, x_6, x_7, x_715);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_st_ref_take(x_3, x_720);
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_ctor_get(x_722, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_722, 1);
lean_inc(x_725);
lean_inc(x_719);
x_726 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_725, x_638, x_719);
x_727 = lean_ctor_get(x_722, 2);
lean_inc(x_727);
x_728 = lean_ctor_get(x_722, 3);
lean_inc(x_728);
x_729 = lean_ctor_get(x_722, 4);
lean_inc(x_729);
x_730 = lean_ctor_get(x_722, 5);
lean_inc(x_730);
x_731 = lean_ctor_get(x_722, 6);
lean_inc(x_731);
x_732 = lean_ctor_get(x_722, 7);
lean_inc(x_732);
x_733 = lean_ctor_get(x_722, 8);
lean_inc(x_733);
x_734 = lean_ctor_get(x_722, 9);
lean_inc(x_734);
x_735 = lean_ctor_get(x_722, 10);
lean_inc(x_735);
x_736 = lean_ctor_get(x_722, 11);
lean_inc(x_736);
lean_dec(x_722);
x_737 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_737, 0, x_724);
lean_ctor_set(x_737, 1, x_726);
lean_ctor_set(x_737, 2, x_727);
lean_ctor_set(x_737, 3, x_728);
lean_ctor_set(x_737, 4, x_729);
lean_ctor_set(x_737, 5, x_730);
lean_ctor_set(x_737, 6, x_731);
lean_ctor_set(x_737, 7, x_732);
lean_ctor_set(x_737, 8, x_733);
lean_ctor_set(x_737, 9, x_734);
lean_ctor_set(x_737, 10, x_735);
lean_ctor_set(x_737, 11, x_736);
x_738 = lean_st_ref_set(x_3, x_737, x_723);
x_739 = lean_ctor_get(x_738, 1);
lean_inc(x_739);
lean_dec(x_738);
x_642 = x_719;
x_643 = x_739;
goto block_711;
}
else
{
uint8_t x_740; 
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_740 = !lean_is_exclusive(x_718);
if (x_740 == 0)
{
return x_718;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_ctor_get(x_718, 0);
x_742 = lean_ctor_get(x_718, 1);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_718);
x_743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_743, 0, x_741);
lean_ctor_set(x_743, 1, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; 
lean_dec(x_638);
x_744 = lean_ctor_get(x_717, 0);
lean_inc(x_744);
lean_dec(x_717);
x_642 = x_744;
x_643 = x_715;
goto block_711;
}
}
}
block_786:
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_753);
x_754 = lean_st_ref_get(x_3, x_8);
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
lean_dec(x_754);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
lean_inc(x_637);
x_758 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_757, x_637);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_637);
x_759 = l_Lean_Meta_Closure_collectExprAux(x_637, x_2, x_3, x_4, x_5, x_6, x_7, x_756);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec(x_759);
x_762 = lean_st_ref_take(x_3, x_761);
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 1);
lean_inc(x_764);
lean_dec(x_762);
x_765 = lean_ctor_get(x_763, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_763, 1);
lean_inc(x_766);
lean_inc(x_760);
x_767 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_766, x_637, x_760);
x_768 = lean_ctor_get(x_763, 2);
lean_inc(x_768);
x_769 = lean_ctor_get(x_763, 3);
lean_inc(x_769);
x_770 = lean_ctor_get(x_763, 4);
lean_inc(x_770);
x_771 = lean_ctor_get(x_763, 5);
lean_inc(x_771);
x_772 = lean_ctor_get(x_763, 6);
lean_inc(x_772);
x_773 = lean_ctor_get(x_763, 7);
lean_inc(x_773);
x_774 = lean_ctor_get(x_763, 8);
lean_inc(x_774);
x_775 = lean_ctor_get(x_763, 9);
lean_inc(x_775);
x_776 = lean_ctor_get(x_763, 10);
lean_inc(x_776);
x_777 = lean_ctor_get(x_763, 11);
lean_inc(x_777);
lean_dec(x_763);
x_778 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_778, 0, x_765);
lean_ctor_set(x_778, 1, x_767);
lean_ctor_set(x_778, 2, x_768);
lean_ctor_set(x_778, 3, x_769);
lean_ctor_set(x_778, 4, x_770);
lean_ctor_set(x_778, 5, x_771);
lean_ctor_set(x_778, 6, x_772);
lean_ctor_set(x_778, 7, x_773);
lean_ctor_set(x_778, 8, x_774);
lean_ctor_set(x_778, 9, x_775);
lean_ctor_set(x_778, 10, x_776);
lean_ctor_set(x_778, 11, x_777);
x_779 = lean_st_ref_set(x_3, x_778, x_764);
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
lean_dec(x_779);
x_640 = x_760;
x_641 = x_780;
goto block_752;
}
else
{
uint8_t x_781; 
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_637);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_781 = !lean_is_exclusive(x_759);
if (x_781 == 0)
{
return x_759;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_759, 0);
x_783 = lean_ctor_get(x_759, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_759);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
else
{
lean_object* x_785; 
lean_dec(x_637);
x_785 = lean_ctor_get(x_758, 0);
lean_inc(x_785);
lean_dec(x_758);
x_640 = x_785;
x_641 = x_756;
goto block_752;
}
}
}
case 10:
{
lean_object* x_793; lean_object* x_794; uint8_t x_828; 
x_793 = lean_ctor_get(x_1, 1);
lean_inc(x_793);
x_828 = l_Lean_Expr_hasLevelParam(x_793);
if (x_828 == 0)
{
uint8_t x_829; 
x_829 = l_Lean_Expr_hasFVar(x_793);
if (x_829 == 0)
{
uint8_t x_830; 
x_830 = l_Lean_Expr_hasMVar(x_793);
if (x_830 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_793;
x_10 = x_8;
goto block_22;
}
else
{
lean_object* x_831; 
x_831 = lean_box(0);
x_794 = x_831;
goto block_827;
}
}
else
{
lean_object* x_832; 
x_832 = lean_box(0);
x_794 = x_832;
goto block_827;
}
}
else
{
lean_object* x_833; 
x_833 = lean_box(0);
x_794 = x_833;
goto block_827;
}
block_827:
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_794);
x_795 = lean_st_ref_get(x_3, x_8);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
lean_inc(x_793);
x_799 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_798, x_793);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; 
lean_inc(x_793);
x_800 = l_Lean_Meta_Closure_collectExprAux(x_793, x_2, x_3, x_4, x_5, x_6, x_7, x_797);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
lean_dec(x_800);
x_803 = lean_st_ref_take(x_3, x_802);
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec(x_803);
x_806 = lean_ctor_get(x_804, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_804, 1);
lean_inc(x_807);
lean_inc(x_801);
x_808 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_807, x_793, x_801);
x_809 = lean_ctor_get(x_804, 2);
lean_inc(x_809);
x_810 = lean_ctor_get(x_804, 3);
lean_inc(x_810);
x_811 = lean_ctor_get(x_804, 4);
lean_inc(x_811);
x_812 = lean_ctor_get(x_804, 5);
lean_inc(x_812);
x_813 = lean_ctor_get(x_804, 6);
lean_inc(x_813);
x_814 = lean_ctor_get(x_804, 7);
lean_inc(x_814);
x_815 = lean_ctor_get(x_804, 8);
lean_inc(x_815);
x_816 = lean_ctor_get(x_804, 9);
lean_inc(x_816);
x_817 = lean_ctor_get(x_804, 10);
lean_inc(x_817);
x_818 = lean_ctor_get(x_804, 11);
lean_inc(x_818);
lean_dec(x_804);
x_819 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_819, 0, x_806);
lean_ctor_set(x_819, 1, x_808);
lean_ctor_set(x_819, 2, x_809);
lean_ctor_set(x_819, 3, x_810);
lean_ctor_set(x_819, 4, x_811);
lean_ctor_set(x_819, 5, x_812);
lean_ctor_set(x_819, 6, x_813);
lean_ctor_set(x_819, 7, x_814);
lean_ctor_set(x_819, 8, x_815);
lean_ctor_set(x_819, 9, x_816);
lean_ctor_set(x_819, 10, x_817);
lean_ctor_set(x_819, 11, x_818);
x_820 = lean_st_ref_set(x_3, x_819, x_805);
x_821 = lean_ctor_get(x_820, 1);
lean_inc(x_821);
lean_dec(x_820);
x_9 = x_801;
x_10 = x_821;
goto block_22;
}
else
{
uint8_t x_822; 
lean_dec(x_793);
lean_dec(x_1);
x_822 = !lean_is_exclusive(x_800);
if (x_822 == 0)
{
return x_800;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_800, 0);
x_824 = lean_ctor_get(x_800, 1);
lean_inc(x_824);
lean_inc(x_823);
lean_dec(x_800);
x_825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
return x_825;
}
}
}
else
{
lean_object* x_826; 
lean_dec(x_793);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_826 = lean_ctor_get(x_799, 0);
lean_inc(x_826);
lean_dec(x_799);
x_9 = x_826;
x_10 = x_797;
goto block_22;
}
}
}
case 11:
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_900; uint8_t x_934; 
x_834 = lean_ctor_get(x_1, 2);
lean_inc(x_834);
x_835 = lean_ctor_get(x_1, 3);
lean_inc(x_835);
x_934 = l_Lean_Expr_hasLevelParam(x_834);
if (x_934 == 0)
{
uint8_t x_935; 
x_935 = l_Lean_Expr_hasFVar(x_834);
if (x_935 == 0)
{
uint8_t x_936; 
x_936 = l_Lean_Expr_hasMVar(x_834);
if (x_936 == 0)
{
x_836 = x_834;
x_837 = x_8;
goto block_899;
}
else
{
lean_object* x_937; 
x_937 = lean_box(0);
x_900 = x_937;
goto block_933;
}
}
else
{
lean_object* x_938; 
x_938 = lean_box(0);
x_900 = x_938;
goto block_933;
}
}
else
{
lean_object* x_939; 
x_939 = lean_box(0);
x_900 = x_939;
goto block_933;
}
block_899:
{
lean_object* x_838; lean_object* x_839; lean_object* x_859; uint8_t x_893; 
x_893 = l_Lean_Expr_hasLevelParam(x_835);
if (x_893 == 0)
{
uint8_t x_894; 
x_894 = l_Lean_Expr_hasFVar(x_835);
if (x_894 == 0)
{
uint8_t x_895; 
x_895 = l_Lean_Expr_hasMVar(x_835);
if (x_895 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_838 = x_835;
x_839 = x_837;
goto block_858;
}
else
{
lean_object* x_896; 
x_896 = lean_box(0);
x_859 = x_896;
goto block_892;
}
}
else
{
lean_object* x_897; 
x_897 = lean_box(0);
x_859 = x_897;
goto block_892;
}
}
else
{
lean_object* x_898; 
x_898 = lean_box(0);
x_859 = x_898;
goto block_892;
}
block_858:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; size_t x_844; size_t x_845; uint8_t x_846; 
x_840 = lean_ctor_get(x_1, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_1, 1);
lean_inc(x_841);
x_842 = lean_ctor_get(x_1, 2);
lean_inc(x_842);
x_843 = lean_ctor_get(x_1, 3);
lean_inc(x_843);
x_844 = lean_ptr_addr(x_842);
lean_dec(x_842);
x_845 = lean_ptr_addr(x_836);
x_846 = lean_usize_dec_eq(x_844, x_845);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_843);
lean_dec(x_1);
x_847 = l_Lean_Expr_proj___override(x_840, x_841, x_836, x_838);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_839);
return x_848;
}
else
{
size_t x_849; size_t x_850; uint8_t x_851; 
x_849 = lean_ptr_addr(x_843);
lean_dec(x_843);
x_850 = lean_ptr_addr(x_838);
x_851 = lean_usize_dec_eq(x_849, x_850);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; 
lean_dec(x_1);
x_852 = l_Lean_Expr_proj___override(x_840, x_841, x_836, x_838);
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_839);
return x_853;
}
else
{
lean_object* x_854; 
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_838);
lean_dec(x_836);
x_854 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_854, 0, x_1);
lean_ctor_set(x_854, 1, x_839);
return x_854;
}
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_1);
x_855 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_856 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_855);
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_839);
return x_857;
}
}
block_892:
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_dec(x_859);
x_860 = lean_st_ref_get(x_3, x_837);
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
lean_inc(x_835);
x_864 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_863, x_835);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; 
lean_inc(x_835);
x_865 = l_Lean_Meta_Closure_collectExprAux(x_835, x_2, x_3, x_4, x_5, x_6, x_7, x_862);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_st_ref_take(x_3, x_867);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
lean_inc(x_866);
x_873 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_872, x_835, x_866);
x_874 = lean_ctor_get(x_869, 2);
lean_inc(x_874);
x_875 = lean_ctor_get(x_869, 3);
lean_inc(x_875);
x_876 = lean_ctor_get(x_869, 4);
lean_inc(x_876);
x_877 = lean_ctor_get(x_869, 5);
lean_inc(x_877);
x_878 = lean_ctor_get(x_869, 6);
lean_inc(x_878);
x_879 = lean_ctor_get(x_869, 7);
lean_inc(x_879);
x_880 = lean_ctor_get(x_869, 8);
lean_inc(x_880);
x_881 = lean_ctor_get(x_869, 9);
lean_inc(x_881);
x_882 = lean_ctor_get(x_869, 10);
lean_inc(x_882);
x_883 = lean_ctor_get(x_869, 11);
lean_inc(x_883);
lean_dec(x_869);
x_884 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_884, 0, x_871);
lean_ctor_set(x_884, 1, x_873);
lean_ctor_set(x_884, 2, x_874);
lean_ctor_set(x_884, 3, x_875);
lean_ctor_set(x_884, 4, x_876);
lean_ctor_set(x_884, 5, x_877);
lean_ctor_set(x_884, 6, x_878);
lean_ctor_set(x_884, 7, x_879);
lean_ctor_set(x_884, 8, x_880);
lean_ctor_set(x_884, 9, x_881);
lean_ctor_set(x_884, 10, x_882);
lean_ctor_set(x_884, 11, x_883);
x_885 = lean_st_ref_set(x_3, x_884, x_870);
x_886 = lean_ctor_get(x_885, 1);
lean_inc(x_886);
lean_dec(x_885);
x_838 = x_866;
x_839 = x_886;
goto block_858;
}
else
{
uint8_t x_887; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_1);
x_887 = !lean_is_exclusive(x_865);
if (x_887 == 0)
{
return x_865;
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_865, 0);
x_889 = lean_ctor_get(x_865, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_865);
x_890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
return x_890;
}
}
}
else
{
lean_object* x_891; 
lean_dec(x_835);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_891 = lean_ctor_get(x_864, 0);
lean_inc(x_891);
lean_dec(x_864);
x_838 = x_891;
x_839 = x_862;
goto block_858;
}
}
}
block_933:
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_900);
x_901 = lean_st_ref_get(x_3, x_8);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec(x_901);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
lean_inc(x_834);
x_905 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_904, x_834);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_834);
x_906 = l_Lean_Meta_Closure_collectExprAux(x_834, x_2, x_3, x_4, x_5, x_6, x_7, x_903);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_906, 1);
lean_inc(x_908);
lean_dec(x_906);
x_909 = lean_st_ref_take(x_3, x_908);
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
lean_dec(x_909);
x_912 = lean_ctor_get(x_910, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_910, 1);
lean_inc(x_913);
lean_inc(x_907);
x_914 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_913, x_834, x_907);
x_915 = lean_ctor_get(x_910, 2);
lean_inc(x_915);
x_916 = lean_ctor_get(x_910, 3);
lean_inc(x_916);
x_917 = lean_ctor_get(x_910, 4);
lean_inc(x_917);
x_918 = lean_ctor_get(x_910, 5);
lean_inc(x_918);
x_919 = lean_ctor_get(x_910, 6);
lean_inc(x_919);
x_920 = lean_ctor_get(x_910, 7);
lean_inc(x_920);
x_921 = lean_ctor_get(x_910, 8);
lean_inc(x_921);
x_922 = lean_ctor_get(x_910, 9);
lean_inc(x_922);
x_923 = lean_ctor_get(x_910, 10);
lean_inc(x_923);
x_924 = lean_ctor_get(x_910, 11);
lean_inc(x_924);
lean_dec(x_910);
x_925 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_925, 0, x_912);
lean_ctor_set(x_925, 1, x_914);
lean_ctor_set(x_925, 2, x_915);
lean_ctor_set(x_925, 3, x_916);
lean_ctor_set(x_925, 4, x_917);
lean_ctor_set(x_925, 5, x_918);
lean_ctor_set(x_925, 6, x_919);
lean_ctor_set(x_925, 7, x_920);
lean_ctor_set(x_925, 8, x_921);
lean_ctor_set(x_925, 9, x_922);
lean_ctor_set(x_925, 10, x_923);
lean_ctor_set(x_925, 11, x_924);
x_926 = lean_st_ref_set(x_3, x_925, x_911);
x_927 = lean_ctor_get(x_926, 1);
lean_inc(x_927);
lean_dec(x_926);
x_836 = x_907;
x_837 = x_927;
goto block_899;
}
else
{
uint8_t x_928; 
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_928 = !lean_is_exclusive(x_906);
if (x_928 == 0)
{
return x_906;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_929 = lean_ctor_get(x_906, 0);
x_930 = lean_ctor_get(x_906, 1);
lean_inc(x_930);
lean_inc(x_929);
lean_dec(x_906);
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_929);
lean_ctor_set(x_931, 1, x_930);
return x_931;
}
}
}
else
{
lean_object* x_932; 
lean_dec(x_834);
x_932 = lean_ctor_get(x_905, 0);
lean_inc(x_932);
lean_dec(x_905);
x_836 = x_932;
x_837 = x_903;
goto block_899;
}
}
}
default: 
{
lean_object* x_940; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_940 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_940, 0, x_1);
lean_ctor_set(x_940, 1, x_8);
return x_940;
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
