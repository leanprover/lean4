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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
size_t l___private_Lean_Data_HashMap_0__Lean_HashMapImp_mkIdx(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__18;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__14;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__9;
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__7;
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__2;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__8;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__4;
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__6;
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__17;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__8;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelParams___default;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__7;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__1;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__3;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__9;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_toProcess___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__19;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__6;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__4;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_6 = (size_t)(x_5) & (lean_unbox(x_4) - 1);
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
x_8 = (size_t)(x_7) & (lean_unbox(x_6) - 1);
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
x_17 = (size_t)(x_16) & (lean_unbox(x_15) - 1);
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
x_9 = (size_t)(x_8) & (lean_unbox(x_7) - 1);
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
x_25 = (size_t)(x_24) & (lean_unbox(x_23) - 1);
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
lean_object* x_10; uint8_t x_98; 
x_98 = l_Lean_Level_hasMVar(x_2);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Level_hasParam(x_2);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_9);
return x_100;
}
else
{
lean_object* x_101; 
x_101 = lean_box(0);
x_10 = x_101;
goto block_97;
}
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
x_10 = x_102;
goto block_97;
}
block_97:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_17, x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_20 = lean_apply_8(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_8, x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_21);
x_30 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_29, x_2, x_21);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_ctor_get(x_26, 2);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
x_42 = lean_ctor_get(x_26, 6);
x_43 = lean_ctor_get(x_26, 7);
x_44 = lean_ctor_get(x_26, 8);
x_45 = lean_ctor_get(x_26, 9);
x_46 = lean_ctor_get(x_26, 10);
x_47 = lean_ctor_get(x_26, 11);
lean_inc(x_47);
lean_inc(x_46);
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
lean_dec(x_26);
lean_inc(x_21);
x_48 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_36, x_2, x_21);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
lean_ctor_set(x_49, 5, x_41);
lean_ctor_set(x_49, 6, x_42);
lean_ctor_set(x_49, 7, x_43);
lean_ctor_set(x_49, 8, x_44);
lean_ctor_set(x_49, 9, x_45);
lean_ctor_set(x_49, 10, x_46);
lean_ctor_set(x_49, 11, x_47);
x_50 = lean_st_ref_set(x_4, x_49, x_27);
lean_dec(x_4);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_58);
return x_13;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_2);
x_62 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_61, x_2);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_64 = lean_apply_8(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_8, x_66);
lean_dec(x_8);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_4, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 11);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 lean_ctor_release(x_70, 9);
 lean_ctor_release(x_70, 10);
 lean_ctor_release(x_70, 11);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
lean_inc(x_65);
x_85 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_72, x_2, x_65);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 12, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
lean_ctor_set(x_86, 2, x_74);
lean_ctor_set(x_86, 3, x_75);
lean_ctor_set(x_86, 4, x_76);
lean_ctor_set(x_86, 5, x_77);
lean_ctor_set(x_86, 6, x_78);
lean_ctor_set(x_86, 7, x_79);
lean_ctor_set(x_86, 8, x_80);
lean_ctor_set(x_86, 9, x_81);
lean_ctor_set(x_86, 10, x_82);
lean_ctor_set(x_86, 11, x_83);
x_87 = lean_st_ref_set(x_4, x_86, x_71);
lean_dec(x_4);
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
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_93 = x_64;
} else {
 lean_dec_ref(x_64);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_62, 0);
lean_inc(x_95);
lean_dec(x_62);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_60);
return x_96;
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
lean_object* x_10; uint8_t x_98; 
x_98 = l_Lean_Expr_hasLevelParam(x_2);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Expr_hasFVar(x_2);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_hasMVar(x_2);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_9);
return x_101;
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
x_10 = x_102;
goto block_97;
}
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_10 = x_103;
goto block_97;
}
}
else
{
lean_object* x_104; 
x_104 = lean_box(0);
x_10 = x_104;
goto block_97;
}
block_97:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_17, x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_20 = lean_apply_8(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_8, x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_21);
x_30 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_29, x_2, x_21);
lean_ctor_set(x_26, 1, x_30);
x_31 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_ctor_get(x_26, 2);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
x_42 = lean_ctor_get(x_26, 6);
x_43 = lean_ctor_get(x_26, 7);
x_44 = lean_ctor_get(x_26, 8);
x_45 = lean_ctor_get(x_26, 9);
x_46 = lean_ctor_get(x_26, 10);
x_47 = lean_ctor_get(x_26, 11);
lean_inc(x_47);
lean_inc(x_46);
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
lean_dec(x_26);
lean_inc(x_21);
x_48 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_37, x_2, x_21);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
lean_ctor_set(x_49, 5, x_41);
lean_ctor_set(x_49, 6, x_42);
lean_ctor_set(x_49, 7, x_43);
lean_ctor_set(x_49, 8, x_44);
lean_ctor_set(x_49, 9, x_45);
lean_ctor_set(x_49, 10, x_46);
lean_ctor_set(x_49, 11, x_47);
x_50 = lean_st_ref_set(x_4, x_49, x_27);
lean_dec(x_4);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_58);
return x_13;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_2);
x_62 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_61, x_2);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_64 = lean_apply_8(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_8, x_66);
lean_dec(x_8);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_4, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 11);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 lean_ctor_release(x_70, 9);
 lean_ctor_release(x_70, 10);
 lean_ctor_release(x_70, 11);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
lean_inc(x_65);
x_85 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_73, x_2, x_65);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 12, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_74);
lean_ctor_set(x_86, 3, x_75);
lean_ctor_set(x_86, 4, x_76);
lean_ctor_set(x_86, 5, x_77);
lean_ctor_set(x_86, 6, x_78);
lean_ctor_set(x_86, 7, x_79);
lean_ctor_set(x_86, 8, x_80);
lean_ctor_set(x_86, 9, x_81);
lean_ctor_set(x_86, 10, x_82);
lean_ctor_set(x_86, 11, x_83);
x_87 = lean_st_ref_set(x_4, x_86, x_71);
lean_dec(x_4);
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
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_93 = x_64;
} else {
 lean_dec_ref(x_64);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_62, 0);
lean_inc(x_95);
lean_dec(x_62);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_60);
return x_96;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
x_16 = lean_name_append_index_after(x_15, x_14);
x_17 = lean_st_ref_get(x_7, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_25 = lean_ctor_get(x_20, 4);
lean_inc(x_16);
x_26 = lean_array_push(x_23, x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_24, x_27);
lean_dec(x_24);
x_29 = lean_array_push(x_25, x_1);
lean_ctor_set(x_20, 4, x_29);
lean_ctor_set(x_20, 3, x_28);
lean_ctor_set(x_20, 2, x_26);
x_30 = lean_st_ref_set(x_3, x_20, x_21);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Level_param___override(x_16);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Level_param___override(x_16);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
x_39 = lean_ctor_get(x_20, 2);
x_40 = lean_ctor_get(x_20, 3);
x_41 = lean_ctor_get(x_20, 4);
x_42 = lean_ctor_get(x_20, 5);
x_43 = lean_ctor_get(x_20, 6);
x_44 = lean_ctor_get(x_20, 7);
x_45 = lean_ctor_get(x_20, 8);
x_46 = lean_ctor_get(x_20, 9);
x_47 = lean_ctor_get(x_20, 10);
x_48 = lean_ctor_get(x_20, 11);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
lean_inc(x_16);
x_49 = lean_array_push(x_39, x_16);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_40, x_50);
lean_dec(x_40);
x_52 = lean_array_push(x_41, x_1);
x_53 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_42);
lean_ctor_set(x_53, 6, x_43);
lean_ctor_set(x_53, 7, x_44);
lean_ctor_set(x_53, 8, x_45);
lean_ctor_set(x_53, 9, x_46);
lean_ctor_set(x_53, 10, x_47);
lean_ctor_set(x_53, 11, x_48);
x_54 = lean_st_ref_set(x_3, x_53, x_21);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Level_param___override(x_16);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
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
lean_object* x_23; lean_object* x_24; uint8_t x_58; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_58 = l_Lean_Level_hasMVar(x_23);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Level_hasParam(x_23);
if (x_59 == 0)
{
x_9 = x_23;
x_10 = x_8;
goto block_21;
}
else
{
lean_object* x_60; 
x_60 = lean_box(0);
x_24 = x_60;
goto block_57;
}
}
else
{
lean_object* x_61; 
x_61 = lean_box(0);
x_24 = x_61;
goto block_57;
}
block_57:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_25 = lean_st_ref_get(x_7, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_23);
x_31 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_30, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_23);
x_32 = l_Lean_Meta_Closure_collectLevelAux(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_7, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_take(x_3, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_inc(x_33);
x_41 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_40, x_23, x_33);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_38, 10);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 11);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_44);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
lean_ctor_set(x_53, 7, x_48);
lean_ctor_set(x_53, 8, x_49);
lean_ctor_set(x_53, 9, x_50);
lean_ctor_set(x_53, 10, x_51);
lean_ctor_set(x_53, 11, x_52);
x_54 = lean_st_ref_set(x_3, x_53, x_39);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_9 = x_33;
x_10 = x_55;
goto block_21;
}
else
{
lean_object* x_56; 
lean_dec(x_23);
x_56 = lean_ctor_get(x_31, 0);
lean_inc(x_56);
lean_dec(x_31);
x_9 = x_56;
x_10 = x_29;
goto block_21;
}
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_125; uint8_t x_159; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_159 = l_Lean_Level_hasMVar(x_62);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Level_hasParam(x_62);
if (x_160 == 0)
{
x_64 = x_62;
x_65 = x_8;
goto block_124;
}
else
{
lean_object* x_161; 
x_161 = lean_box(0);
x_125 = x_161;
goto block_158;
}
}
else
{
lean_object* x_162; 
x_162 = lean_box(0);
x_125 = x_162;
goto block_158;
}
block_124:
{
lean_object* x_66; lean_object* x_67; lean_object* x_86; uint8_t x_120; 
x_120 = l_Lean_Level_hasMVar(x_63);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = l_Lean_Level_hasParam(x_63);
if (x_121 == 0)
{
x_66 = x_63;
x_67 = x_65;
goto block_85;
}
else
{
lean_object* x_122; 
x_122 = lean_box(0);
x_86 = x_122;
goto block_119;
}
}
else
{
lean_object* x_123; 
x_123 = lean_box(0);
x_86 = x_123;
goto block_119;
}
block_85:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_71 = lean_ptr_addr(x_64);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_1);
x_73 = l_Lean_mkLevelMax_x27(x_64, x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_69);
lean_dec(x_69);
x_76 = lean_ptr_addr(x_66);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = l_Lean_mkLevelMax_x27(x_64, x_66);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_67);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_simpLevelMax_x27(x_64, x_66, x_1);
lean_dec(x_1);
lean_dec(x_66);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_67);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_1);
x_82 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_83 = l_panic___at_Lean_Level_normalize___spec__1(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_67);
return x_84;
}
}
block_119:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
x_87 = lean_st_ref_get(x_7, x_65);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_get(x_3, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_63);
x_93 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_92, x_63);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_63);
x_94 = l_Lean_Meta_Closure_collectLevelAux(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_91);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_7, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_take(x_3, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_inc(x_95);
x_103 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_102, x_63, x_95);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 5);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 6);
lean_inc(x_109);
x_110 = lean_ctor_get(x_100, 7);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 8);
lean_inc(x_111);
x_112 = lean_ctor_get(x_100, 9);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 10);
lean_inc(x_113);
x_114 = lean_ctor_get(x_100, 11);
lean_inc(x_114);
lean_dec(x_100);
x_115 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_104);
lean_ctor_set(x_115, 2, x_105);
lean_ctor_set(x_115, 3, x_106);
lean_ctor_set(x_115, 4, x_107);
lean_ctor_set(x_115, 5, x_108);
lean_ctor_set(x_115, 6, x_109);
lean_ctor_set(x_115, 7, x_110);
lean_ctor_set(x_115, 8, x_111);
lean_ctor_set(x_115, 9, x_112);
lean_ctor_set(x_115, 10, x_113);
lean_ctor_set(x_115, 11, x_114);
x_116 = lean_st_ref_set(x_3, x_115, x_101);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_66 = x_95;
x_67 = x_117;
goto block_85;
}
else
{
lean_object* x_118; 
lean_dec(x_63);
x_118 = lean_ctor_get(x_93, 0);
lean_inc(x_118);
lean_dec(x_93);
x_66 = x_118;
x_67 = x_91;
goto block_85;
}
}
}
block_158:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_125);
x_126 = lean_st_ref_get(x_7, x_8);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_get(x_3, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_62);
x_132 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_131, x_62);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_inc(x_62);
x_133 = l_Lean_Meta_Closure_collectLevelAux(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_st_ref_get(x_7, x_135);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_st_ref_take(x_3, x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_inc(x_134);
x_142 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_141, x_62, x_134);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_139, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_139, 5);
lean_inc(x_147);
x_148 = lean_ctor_get(x_139, 6);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 7);
lean_inc(x_149);
x_150 = lean_ctor_get(x_139, 8);
lean_inc(x_150);
x_151 = lean_ctor_get(x_139, 9);
lean_inc(x_151);
x_152 = lean_ctor_get(x_139, 10);
lean_inc(x_152);
x_153 = lean_ctor_get(x_139, 11);
lean_inc(x_153);
lean_dec(x_139);
x_154 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_143);
lean_ctor_set(x_154, 2, x_144);
lean_ctor_set(x_154, 3, x_145);
lean_ctor_set(x_154, 4, x_146);
lean_ctor_set(x_154, 5, x_147);
lean_ctor_set(x_154, 6, x_148);
lean_ctor_set(x_154, 7, x_149);
lean_ctor_set(x_154, 8, x_150);
lean_ctor_set(x_154, 9, x_151);
lean_ctor_set(x_154, 10, x_152);
lean_ctor_set(x_154, 11, x_153);
x_155 = lean_st_ref_set(x_3, x_154, x_140);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_64 = x_134;
x_65 = x_156;
goto block_124;
}
else
{
lean_object* x_157; 
lean_dec(x_62);
x_157 = lean_ctor_get(x_132, 0);
lean_inc(x_157);
lean_dec(x_132);
x_64 = x_157;
x_65 = x_130;
goto block_124;
}
}
}
case 3:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_226; uint8_t x_260; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_inc(x_164);
x_260 = l_Lean_Level_hasMVar(x_163);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = l_Lean_Level_hasParam(x_163);
if (x_261 == 0)
{
x_165 = x_163;
x_166 = x_8;
goto block_225;
}
else
{
lean_object* x_262; 
x_262 = lean_box(0);
x_226 = x_262;
goto block_259;
}
}
else
{
lean_object* x_263; 
x_263 = lean_box(0);
x_226 = x_263;
goto block_259;
}
block_225:
{
lean_object* x_167; lean_object* x_168; lean_object* x_187; uint8_t x_221; 
x_221 = l_Lean_Level_hasMVar(x_164);
if (x_221 == 0)
{
uint8_t x_222; 
x_222 = l_Lean_Level_hasParam(x_164);
if (x_222 == 0)
{
x_167 = x_164;
x_168 = x_166;
goto block_186;
}
else
{
lean_object* x_223; 
x_223 = lean_box(0);
x_187 = x_223;
goto block_220;
}
}
else
{
lean_object* x_224; 
x_224 = lean_box(0);
x_187 = x_224;
goto block_220;
}
block_186:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_1, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 1);
lean_inc(x_170);
x_171 = lean_ptr_addr(x_169);
lean_dec(x_169);
x_172 = lean_ptr_addr(x_165);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_170);
lean_dec(x_1);
x_174 = l_Lean_mkLevelIMax_x27(x_165, x_167);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_168);
return x_175;
}
else
{
size_t x_176; size_t x_177; uint8_t x_178; 
x_176 = lean_ptr_addr(x_170);
lean_dec(x_170);
x_177 = lean_ptr_addr(x_167);
x_178 = lean_usize_dec_eq(x_176, x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_1);
x_179 = l_Lean_mkLevelIMax_x27(x_165, x_167);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_168);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = l_Lean_simpLevelIMax_x27(x_165, x_167, x_1);
lean_dec(x_1);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_168);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_1);
x_183 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_184 = l_panic___at_Lean_Level_normalize___spec__1(x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
return x_185;
}
}
block_220:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_187);
x_188 = lean_st_ref_get(x_7, x_166);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_st_ref_get(x_3, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_164);
x_194 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_193, x_164);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_inc(x_164);
x_195 = l_Lean_Meta_Closure_collectLevelAux(x_164, x_2, x_3, x_4, x_5, x_6, x_7, x_192);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_st_ref_get(x_7, x_197);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_3, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
lean_inc(x_196);
x_204 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_203, x_164, x_196);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 4);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 5);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 6);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 7);
lean_inc(x_211);
x_212 = lean_ctor_get(x_201, 8);
lean_inc(x_212);
x_213 = lean_ctor_get(x_201, 9);
lean_inc(x_213);
x_214 = lean_ctor_get(x_201, 10);
lean_inc(x_214);
x_215 = lean_ctor_get(x_201, 11);
lean_inc(x_215);
lean_dec(x_201);
x_216 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_216, 0, x_204);
lean_ctor_set(x_216, 1, x_205);
lean_ctor_set(x_216, 2, x_206);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_208);
lean_ctor_set(x_216, 5, x_209);
lean_ctor_set(x_216, 6, x_210);
lean_ctor_set(x_216, 7, x_211);
lean_ctor_set(x_216, 8, x_212);
lean_ctor_set(x_216, 9, x_213);
lean_ctor_set(x_216, 10, x_214);
lean_ctor_set(x_216, 11, x_215);
x_217 = lean_st_ref_set(x_3, x_216, x_202);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_167 = x_196;
x_168 = x_218;
goto block_186;
}
else
{
lean_object* x_219; 
lean_dec(x_164);
x_219 = lean_ctor_get(x_194, 0);
lean_inc(x_219);
lean_dec(x_194);
x_167 = x_219;
x_168 = x_192;
goto block_186;
}
}
}
block_259:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_226);
x_227 = lean_st_ref_get(x_7, x_8);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_st_ref_get(x_3, x_228);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_163);
x_233 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_232, x_163);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_inc(x_163);
x_234 = l_Lean_Meta_Closure_collectLevelAux(x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_231);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_st_ref_get(x_7, x_236);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_st_ref_take(x_3, x_238);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_inc(x_235);
x_243 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_242, x_163, x_235);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_240, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_240, 5);
lean_inc(x_248);
x_249 = lean_ctor_get(x_240, 6);
lean_inc(x_249);
x_250 = lean_ctor_get(x_240, 7);
lean_inc(x_250);
x_251 = lean_ctor_get(x_240, 8);
lean_inc(x_251);
x_252 = lean_ctor_get(x_240, 9);
lean_inc(x_252);
x_253 = lean_ctor_get(x_240, 10);
lean_inc(x_253);
x_254 = lean_ctor_get(x_240, 11);
lean_inc(x_254);
lean_dec(x_240);
x_255 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_255, 0, x_243);
lean_ctor_set(x_255, 1, x_244);
lean_ctor_set(x_255, 2, x_245);
lean_ctor_set(x_255, 3, x_246);
lean_ctor_set(x_255, 4, x_247);
lean_ctor_set(x_255, 5, x_248);
lean_ctor_set(x_255, 6, x_249);
lean_ctor_set(x_255, 7, x_250);
lean_ctor_set(x_255, 8, x_251);
lean_ctor_set(x_255, 9, x_252);
lean_ctor_set(x_255, 10, x_253);
lean_ctor_set(x_255, 11, x_254);
x_256 = lean_st_ref_set(x_3, x_255, x_241);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_165 = x_235;
x_166 = x_257;
goto block_225;
}
else
{
lean_object* x_258; 
lean_dec(x_163);
x_258 = lean_ctor_get(x_233, 0);
lean_inc(x_258);
lean_dec(x_233);
x_165 = x_258;
x_166 = x_231;
goto block_225;
}
}
}
default: 
{
lean_object* x_264; 
x_264 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_264;
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
lean_object* x_9; uint8_t x_87; 
x_87 = l_Lean_Level_hasMVar(x_1);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Level_hasParam(x_1);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_8);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_9 = x_90;
goto block_86;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_9 = x_91;
goto block_86;
}
block_86:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_12);
lean_inc(x_1);
x_18 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_7, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
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
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_19);
x_28 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_27, x_1, x_19);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_19);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
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
lean_inc(x_19);
x_46 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_34, x_1, x_19);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
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
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_17, 0);
lean_inc(x_52);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_52);
return x_12;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_1);
x_56 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_55, x_1);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_1);
x_57 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_7, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_take(x_3, x_61);
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
lean_inc(x_58);
x_78 = l_Lean_HashMap_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_65, x_1, x_58);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 12, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_66);
lean_ctor_set(x_79, 2, x_67);
lean_ctor_set(x_79, 3, x_68);
lean_ctor_set(x_79, 4, x_69);
lean_ctor_set(x_79, 5, x_70);
lean_ctor_set(x_79, 6, x_71);
lean_ctor_set(x_79, 7, x_72);
lean_ctor_set(x_79, 8, x_73);
lean_ctor_set(x_79, 9, x_74);
lean_ctor_set(x_79, 10, x_75);
lean_ctor_set(x_79, 11, x_76);
x_80 = lean_st_ref_set(x_3, x_79, x_64);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_58);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_56, 0);
lean_inc(x_84);
lean_dec(x_56);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_54);
return x_85;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVarsCore(x_16, x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_19);
x_27 = lean_st_ref_set(x_5, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_18);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_st_ref_set(x_5, x_35, x_24);
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_37);
return x_39;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 8);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
x_14 = lean_name_append_index_after(x_13, x_12);
x_15 = lean_st_ref_get(x_5, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_18, 8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
lean_ctor_set(x_18, 8, x_23);
x_24 = lean_st_ref_set(x_1, x_18, x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_14);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
x_33 = lean_ctor_get(x_18, 4);
x_34 = lean_ctor_get(x_18, 5);
x_35 = lean_ctor_get(x_18, 6);
x_36 = lean_ctor_get(x_18, 7);
x_37 = lean_ctor_get(x_18, 8);
x_38 = lean_ctor_get(x_18, 9);
x_39 = lean_ctor_get(x_18, 10);
x_40 = lean_ctor_get(x_18, 11);
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
lean_inc(x_29);
lean_dec(x_18);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_37, x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_33);
lean_ctor_set(x_43, 5, x_34);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_42);
lean_ctor_set(x_43, 9, x_38);
lean_ctor_set(x_43, 10, x_39);
lean_ctor_set(x_43, 11, x_40);
x_44 = lean_st_ref_set(x_1, x_43, x_19);
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
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_45);
return x_47;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 11);
x_16 = lean_array_push(x_15, x_1);
lean_ctor_set(x_12, 11, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get(x_12, 7);
x_32 = lean_ctor_get(x_12, 8);
x_33 = lean_ctor_get(x_12, 9);
x_34 = lean_ctor_get(x_12, 10);
x_35 = lean_ctor_get(x_12, 11);
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
lean_dec(x_12);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
lean_ctor_set(x_37, 9, x_33);
lean_ctor_set(x_37, 10, x_34);
lean_ctor_set(x_37, 11, x_36);
x_38 = lean_st_ref_set(x_3, x_37, x_13);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
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
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_149; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_149 = l_Lean_Expr_hasLevelParam(x_69);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasFVar(x_69);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasMVar(x_69);
if (x_151 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_67;
}
else
{
lean_object* x_152; 
lean_free_object(x_67);
x_152 = lean_box(0);
x_71 = x_152;
goto block_148;
}
}
else
{
lean_object* x_153; 
lean_free_object(x_67);
x_153 = lean_box(0);
x_71 = x_153;
goto block_148;
}
}
else
{
lean_object* x_154; 
lean_free_object(x_67);
x_154 = lean_box(0);
x_71 = x_154;
goto block_148;
}
block_148:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_71);
x_72 = lean_st_ref_get(x_7, x_70);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_get(x_3, x_73);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_69);
x_79 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_78, x_69);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_free_object(x_74);
lean_inc(x_7);
lean_inc(x_69);
x_80 = l_Lean_Meta_Closure_collectExprAux(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_7, x_82);
lean_dec(x_7);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_st_ref_take(x_3, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_inc(x_81);
x_90 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_89, x_69, x_81);
x_91 = lean_ctor_get(x_86, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 6);
lean_inc(x_95);
x_96 = lean_ctor_get(x_86, 7);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 8);
lean_inc(x_97);
x_98 = lean_ctor_get(x_86, 9);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 10);
lean_inc(x_99);
x_100 = lean_ctor_get(x_86, 11);
lean_inc(x_100);
lean_dec(x_86);
x_101 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_101, 0, x_88);
lean_ctor_set(x_101, 1, x_90);
lean_ctor_set(x_101, 2, x_91);
lean_ctor_set(x_101, 3, x_92);
lean_ctor_set(x_101, 4, x_93);
lean_ctor_set(x_101, 5, x_94);
lean_ctor_set(x_101, 6, x_95);
lean_ctor_set(x_101, 7, x_96);
lean_ctor_set(x_101, 8, x_97);
lean_ctor_set(x_101, 9, x_98);
lean_ctor_set(x_101, 10, x_99);
lean_ctor_set(x_101, 11, x_100);
x_102 = lean_st_ref_set(x_3, x_101, x_87);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_81);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_81);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_69);
lean_dec(x_7);
x_107 = !lean_is_exclusive(x_80);
if (x_107 == 0)
{
return x_80;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_80, 0);
x_109 = lean_ctor_get(x_80, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_80);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_69);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = lean_ctor_get(x_79, 0);
lean_inc(x_111);
lean_dec(x_79);
lean_ctor_set(x_74, 0, x_111);
return x_74;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_74, 0);
x_113 = lean_ctor_get(x_74, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_74);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_69);
x_115 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_114, x_69);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_inc(x_7);
lean_inc(x_69);
x_116 = l_Lean_Meta_Closure_collectExprAux(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_7, x_118);
lean_dec(x_7);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_take(x_3, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_inc(x_117);
x_126 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_125, x_69, x_117);
x_127 = lean_ctor_get(x_122, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 5);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 6);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 7);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 8);
lean_inc(x_133);
x_134 = lean_ctor_get(x_122, 9);
lean_inc(x_134);
x_135 = lean_ctor_get(x_122, 10);
lean_inc(x_135);
x_136 = lean_ctor_get(x_122, 11);
lean_inc(x_136);
lean_dec(x_122);
x_137 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_126);
lean_ctor_set(x_137, 2, x_127);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set(x_137, 4, x_129);
lean_ctor_set(x_137, 5, x_130);
lean_ctor_set(x_137, 6, x_131);
lean_ctor_set(x_137, 7, x_132);
lean_ctor_set(x_137, 8, x_133);
lean_ctor_set(x_137, 9, x_134);
lean_ctor_set(x_137, 10, x_135);
lean_ctor_set(x_137, 11, x_136);
x_138 = lean_st_ref_set(x_3, x_137, x_123);
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
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_117);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_69);
lean_dec(x_7);
x_142 = lean_ctor_get(x_116, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_116, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_144 = x_116;
} else {
 lean_dec_ref(x_116);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_69);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_146 = lean_ctor_get(x_115, 0);
lean_inc(x_146);
lean_dec(x_115);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_113);
return x_147;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_199; 
x_155 = lean_ctor_get(x_67, 0);
x_156 = lean_ctor_get(x_67, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_67);
x_199 = l_Lean_Expr_hasLevelParam(x_155);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = l_Lean_Expr_hasFVar(x_155);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l_Lean_Expr_hasMVar(x_155);
if (x_201 == 0)
{
lean_object* x_202; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_155);
lean_ctor_set(x_202, 1, x_156);
return x_202;
}
else
{
lean_object* x_203; 
x_203 = lean_box(0);
x_157 = x_203;
goto block_198;
}
}
else
{
lean_object* x_204; 
x_204 = lean_box(0);
x_157 = x_204;
goto block_198;
}
}
else
{
lean_object* x_205; 
x_205 = lean_box(0);
x_157 = x_205;
goto block_198;
}
block_198:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_157);
x_158 = lean_st_ref_get(x_7, x_156);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_st_ref_get(x_3, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
lean_inc(x_155);
x_165 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_164, x_155);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
lean_dec(x_163);
lean_inc(x_7);
lean_inc(x_155);
x_166 = l_Lean_Meta_Closure_collectExprAux(x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_162);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_st_ref_get(x_7, x_168);
lean_dec(x_7);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_3, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_inc(x_167);
x_176 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_175, x_155, x_167);
x_177 = lean_ctor_get(x_172, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 5);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 6);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 7);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 8);
lean_inc(x_183);
x_184 = lean_ctor_get(x_172, 9);
lean_inc(x_184);
x_185 = lean_ctor_get(x_172, 10);
lean_inc(x_185);
x_186 = lean_ctor_get(x_172, 11);
lean_inc(x_186);
lean_dec(x_172);
x_187 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_176);
lean_ctor_set(x_187, 2, x_177);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set(x_187, 4, x_179);
lean_ctor_set(x_187, 5, x_180);
lean_ctor_set(x_187, 6, x_181);
lean_ctor_set(x_187, 7, x_182);
lean_ctor_set(x_187, 8, x_183);
lean_ctor_set(x_187, 9, x_184);
lean_ctor_set(x_187, 10, x_185);
lean_ctor_set(x_187, 11, x_186);
x_188 = lean_st_ref_set(x_3, x_187, x_173);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_167);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_155);
lean_dec(x_7);
x_192 = lean_ctor_get(x_166, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_166, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_194 = x_166;
} else {
 lean_dec_ref(x_166);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_155);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_196 = lean_ctor_get(x_165, 0);
lean_inc(x_196);
lean_dec(x_165);
if (lean_is_scalar(x_163)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_163;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_162);
return x_197;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_206 = !lean_is_exclusive(x_67);
if (x_206 == 0)
{
return x_67;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_67, 0);
x_208 = lean_ctor_get(x_67, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_67);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_210 = !lean_is_exclusive(x_39);
if (x_210 == 0)
{
return x_39;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_39, 0);
x_212 = lean_ctor_get(x_39, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_39);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
case 2:
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_1, 0);
lean_inc(x_214);
x_215 = l_Lean_MVarId_getDecl(x_214, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 2);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_219 = l_Lean_Meta_Closure_preprocess(x_218, x_2, x_3, x_4, x_5, x_6, x_7, x_217);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_262; uint8_t x_300; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_300 = l_Lean_Expr_hasLevelParam(x_220);
if (x_300 == 0)
{
uint8_t x_301; 
x_301 = l_Lean_Expr_hasFVar(x_220);
if (x_301 == 0)
{
uint8_t x_302; 
x_302 = l_Lean_Expr_hasMVar(x_220);
if (x_302 == 0)
{
x_222 = x_220;
x_223 = x_221;
goto block_261;
}
else
{
lean_object* x_303; 
x_303 = lean_box(0);
x_262 = x_303;
goto block_299;
}
}
else
{
lean_object* x_304; 
x_304 = lean_box(0);
x_262 = x_304;
goto block_299;
}
}
else
{
lean_object* x_305; 
x_305 = lean_box(0);
x_262 = x_305;
goto block_299;
}
block_261:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_224 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_st_ref_get(x_7, x_229);
lean_dec(x_7);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_st_ref_take(x_3, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 3);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 4);
lean_inc(x_239);
x_240 = lean_ctor_get(x_233, 5);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 6);
lean_inc(x_241);
x_242 = lean_unsigned_to_nat(0u);
x_243 = 0;
x_244 = 0;
lean_inc(x_225);
x_245 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_225);
lean_ctor_set(x_245, 2, x_228);
lean_ctor_set(x_245, 3, x_222);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*4 + 1, x_244);
x_246 = lean_array_push(x_241, x_245);
x_247 = lean_ctor_get(x_233, 7);
lean_inc(x_247);
x_248 = lean_ctor_get(x_233, 8);
lean_inc(x_248);
x_249 = lean_ctor_get(x_233, 9);
lean_inc(x_249);
x_250 = lean_array_push(x_249, x_1);
x_251 = lean_ctor_get(x_233, 10);
lean_inc(x_251);
x_252 = lean_ctor_get(x_233, 11);
lean_inc(x_252);
lean_dec(x_233);
x_253 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_253, 0, x_235);
lean_ctor_set(x_253, 1, x_236);
lean_ctor_set(x_253, 2, x_237);
lean_ctor_set(x_253, 3, x_238);
lean_ctor_set(x_253, 4, x_239);
lean_ctor_set(x_253, 5, x_240);
lean_ctor_set(x_253, 6, x_246);
lean_ctor_set(x_253, 7, x_247);
lean_ctor_set(x_253, 8, x_248);
lean_ctor_set(x_253, 9, x_250);
lean_ctor_set(x_253, 10, x_251);
lean_ctor_set(x_253, 11, x_252);
x_254 = lean_st_ref_set(x_3, x_253, x_234);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_254, 0);
lean_dec(x_256);
x_257 = l_Lean_Expr_fvar___override(x_225);
lean_ctor_set(x_254, 0, x_257);
return x_254;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
lean_dec(x_254);
x_259 = l_Lean_Expr_fvar___override(x_225);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
block_299:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_262);
x_263 = lean_st_ref_get(x_7, x_221);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_st_ref_get(x_3, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_220);
x_269 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_268, x_220);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_220);
x_270 = l_Lean_Meta_Closure_collectExprAux(x_220, x_2, x_3, x_4, x_5, x_6, x_7, x_267);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_st_ref_get(x_7, x_272);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_st_ref_take(x_3, x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_inc(x_271);
x_280 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_279, x_220, x_271);
x_281 = lean_ctor_get(x_276, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_276, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_276, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_276, 5);
lean_inc(x_284);
x_285 = lean_ctor_get(x_276, 6);
lean_inc(x_285);
x_286 = lean_ctor_get(x_276, 7);
lean_inc(x_286);
x_287 = lean_ctor_get(x_276, 8);
lean_inc(x_287);
x_288 = lean_ctor_get(x_276, 9);
lean_inc(x_288);
x_289 = lean_ctor_get(x_276, 10);
lean_inc(x_289);
x_290 = lean_ctor_get(x_276, 11);
lean_inc(x_290);
lean_dec(x_276);
x_291 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_291, 0, x_278);
lean_ctor_set(x_291, 1, x_280);
lean_ctor_set(x_291, 2, x_281);
lean_ctor_set(x_291, 3, x_282);
lean_ctor_set(x_291, 4, x_283);
lean_ctor_set(x_291, 5, x_284);
lean_ctor_set(x_291, 6, x_285);
lean_ctor_set(x_291, 7, x_286);
lean_ctor_set(x_291, 8, x_287);
lean_ctor_set(x_291, 9, x_288);
lean_ctor_set(x_291, 10, x_289);
lean_ctor_set(x_291, 11, x_290);
x_292 = lean_st_ref_set(x_3, x_291, x_277);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_222 = x_271;
x_223 = x_293;
goto block_261;
}
else
{
uint8_t x_294; 
lean_dec(x_220);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_270);
if (x_294 == 0)
{
return x_270;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_270, 0);
x_296 = lean_ctor_get(x_270, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_270);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; 
lean_dec(x_220);
x_298 = lean_ctor_get(x_269, 0);
lean_inc(x_298);
lean_dec(x_269);
x_222 = x_298;
x_223 = x_267;
goto block_261;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_219);
if (x_306 == 0)
{
return x_219;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_219, 0);
x_308 = lean_ctor_get(x_219, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_219);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_215);
if (x_310 == 0)
{
return x_215;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_215, 0);
x_312 = lean_ctor_get(x_215, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_215);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
case 3:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_1, 0);
lean_inc(x_314);
lean_inc(x_314);
x_315 = l_Lean_Meta_Closure_collectLevel(x_314, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; size_t x_318; size_t x_319; uint8_t x_320; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = lean_ptr_addr(x_314);
lean_dec(x_314);
x_319 = lean_ptr_addr(x_317);
x_320 = lean_usize_dec_eq(x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_1);
x_321 = l_Lean_Expr_sort___override(x_317);
lean_ctor_set(x_315, 0, x_321);
return x_315;
}
else
{
lean_dec(x_317);
lean_ctor_set(x_315, 0, x_1);
return x_315;
}
}
else
{
lean_object* x_322; lean_object* x_323; size_t x_324; size_t x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_315, 0);
x_323 = lean_ctor_get(x_315, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_315);
x_324 = lean_ptr_addr(x_314);
lean_dec(x_314);
x_325 = lean_ptr_addr(x_322);
x_326 = lean_usize_dec_eq(x_324, x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_1);
x_327 = l_Lean_Expr_sort___override(x_322);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_323);
return x_328;
}
else
{
lean_object* x_329; 
lean_dec(x_322);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_1);
lean_ctor_set(x_329, 1, x_323);
return x_329;
}
}
}
case 4:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_330 = lean_ctor_get(x_1, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_1, 1);
lean_inc(x_331);
x_332 = lean_box(0);
lean_inc(x_331);
x_333 = l_List_mapM_loop___at_Lean_Meta_Closure_collectExprAux___spec__3(x_331, x_332, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_333, 0);
x_336 = l_ptrEqList___rarg(x_331, x_335);
lean_dec(x_331);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_1);
x_337 = l_Lean_Expr_const___override(x_330, x_335);
lean_ctor_set(x_333, 0, x_337);
return x_333;
}
else
{
lean_dec(x_335);
lean_dec(x_330);
lean_ctor_set(x_333, 0, x_1);
return x_333;
}
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_ctor_get(x_333, 0);
x_339 = lean_ctor_get(x_333, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_333);
x_340 = l_ptrEqList___rarg(x_331, x_338);
lean_dec(x_331);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_1);
x_341 = l_Lean_Expr_const___override(x_330, x_338);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_339);
return x_342;
}
else
{
lean_object* x_343; 
lean_dec(x_338);
lean_dec(x_330);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_1);
lean_ctor_set(x_343, 1, x_339);
return x_343;
}
}
}
case 5:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_412; uint8_t x_450; 
x_344 = lean_ctor_get(x_1, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_1, 1);
lean_inc(x_345);
x_450 = l_Lean_Expr_hasLevelParam(x_344);
if (x_450 == 0)
{
uint8_t x_451; 
x_451 = l_Lean_Expr_hasFVar(x_344);
if (x_451 == 0)
{
uint8_t x_452; 
x_452 = l_Lean_Expr_hasMVar(x_344);
if (x_452 == 0)
{
x_346 = x_344;
x_347 = x_8;
goto block_411;
}
else
{
lean_object* x_453; 
x_453 = lean_box(0);
x_412 = x_453;
goto block_449;
}
}
else
{
lean_object* x_454; 
x_454 = lean_box(0);
x_412 = x_454;
goto block_449;
}
}
else
{
lean_object* x_455; 
x_455 = lean_box(0);
x_412 = x_455;
goto block_449;
}
block_411:
{
lean_object* x_348; lean_object* x_349; lean_object* x_367; uint8_t x_405; 
x_405 = l_Lean_Expr_hasLevelParam(x_345);
if (x_405 == 0)
{
uint8_t x_406; 
x_406 = l_Lean_Expr_hasFVar(x_345);
if (x_406 == 0)
{
uint8_t x_407; 
x_407 = l_Lean_Expr_hasMVar(x_345);
if (x_407 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_348 = x_345;
x_349 = x_347;
goto block_366;
}
else
{
lean_object* x_408; 
x_408 = lean_box(0);
x_367 = x_408;
goto block_404;
}
}
else
{
lean_object* x_409; 
x_409 = lean_box(0);
x_367 = x_409;
goto block_404;
}
}
else
{
lean_object* x_410; 
x_410 = lean_box(0);
x_367 = x_410;
goto block_404;
}
block_366:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_350; lean_object* x_351; size_t x_352; size_t x_353; uint8_t x_354; 
x_350 = lean_ctor_get(x_1, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_1, 1);
lean_inc(x_351);
x_352 = lean_ptr_addr(x_350);
lean_dec(x_350);
x_353 = lean_ptr_addr(x_346);
x_354 = lean_usize_dec_eq(x_352, x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_351);
lean_dec(x_1);
x_355 = l_Lean_Expr_app___override(x_346, x_348);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_349);
return x_356;
}
else
{
size_t x_357; size_t x_358; uint8_t x_359; 
x_357 = lean_ptr_addr(x_351);
lean_dec(x_351);
x_358 = lean_ptr_addr(x_348);
x_359 = lean_usize_dec_eq(x_357, x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_1);
x_360 = l_Lean_Expr_app___override(x_346, x_348);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_349);
return x_361;
}
else
{
lean_object* x_362; 
lean_dec(x_348);
lean_dec(x_346);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_349);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_1);
x_363 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_364 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_349);
return x_365;
}
}
block_404:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_367);
x_368 = lean_st_ref_get(x_7, x_347);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_st_ref_get(x_3, x_369);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
lean_inc(x_345);
x_374 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_373, x_345);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
lean_inc(x_7);
lean_inc(x_345);
x_375 = l_Lean_Meta_Closure_collectExprAux(x_345, x_2, x_3, x_4, x_5, x_6, x_7, x_372);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_st_ref_get(x_7, x_377);
lean_dec(x_7);
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_st_ref_take(x_3, x_379);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
lean_inc(x_376);
x_385 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_384, x_345, x_376);
x_386 = lean_ctor_get(x_381, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_381, 3);
lean_inc(x_387);
x_388 = lean_ctor_get(x_381, 4);
lean_inc(x_388);
x_389 = lean_ctor_get(x_381, 5);
lean_inc(x_389);
x_390 = lean_ctor_get(x_381, 6);
lean_inc(x_390);
x_391 = lean_ctor_get(x_381, 7);
lean_inc(x_391);
x_392 = lean_ctor_get(x_381, 8);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 9);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 10);
lean_inc(x_394);
x_395 = lean_ctor_get(x_381, 11);
lean_inc(x_395);
lean_dec(x_381);
x_396 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_385);
lean_ctor_set(x_396, 2, x_386);
lean_ctor_set(x_396, 3, x_387);
lean_ctor_set(x_396, 4, x_388);
lean_ctor_set(x_396, 5, x_389);
lean_ctor_set(x_396, 6, x_390);
lean_ctor_set(x_396, 7, x_391);
lean_ctor_set(x_396, 8, x_392);
lean_ctor_set(x_396, 9, x_393);
lean_ctor_set(x_396, 10, x_394);
lean_ctor_set(x_396, 11, x_395);
x_397 = lean_st_ref_set(x_3, x_396, x_382);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_348 = x_376;
x_349 = x_398;
goto block_366;
}
else
{
uint8_t x_399; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_7);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_375);
if (x_399 == 0)
{
return x_375;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_375, 0);
x_401 = lean_ctor_get(x_375, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_375);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
else
{
lean_object* x_403; 
lean_dec(x_345);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_403 = lean_ctor_get(x_374, 0);
lean_inc(x_403);
lean_dec(x_374);
x_348 = x_403;
x_349 = x_372;
goto block_366;
}
}
}
block_449:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_412);
x_413 = lean_st_ref_get(x_7, x_8);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_st_ref_get(x_3, x_414);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
lean_inc(x_344);
x_419 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_418, x_344);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_344);
x_420 = l_Lean_Meta_Closure_collectExprAux(x_344, x_2, x_3, x_4, x_5, x_6, x_7, x_417);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_st_ref_get(x_7, x_422);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_st_ref_take(x_3, x_424);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
lean_inc(x_421);
x_430 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_429, x_344, x_421);
x_431 = lean_ctor_get(x_426, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_426, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_426, 4);
lean_inc(x_433);
x_434 = lean_ctor_get(x_426, 5);
lean_inc(x_434);
x_435 = lean_ctor_get(x_426, 6);
lean_inc(x_435);
x_436 = lean_ctor_get(x_426, 7);
lean_inc(x_436);
x_437 = lean_ctor_get(x_426, 8);
lean_inc(x_437);
x_438 = lean_ctor_get(x_426, 9);
lean_inc(x_438);
x_439 = lean_ctor_get(x_426, 10);
lean_inc(x_439);
x_440 = lean_ctor_get(x_426, 11);
lean_inc(x_440);
lean_dec(x_426);
x_441 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_441, 0, x_428);
lean_ctor_set(x_441, 1, x_430);
lean_ctor_set(x_441, 2, x_431);
lean_ctor_set(x_441, 3, x_432);
lean_ctor_set(x_441, 4, x_433);
lean_ctor_set(x_441, 5, x_434);
lean_ctor_set(x_441, 6, x_435);
lean_ctor_set(x_441, 7, x_436);
lean_ctor_set(x_441, 8, x_437);
lean_ctor_set(x_441, 9, x_438);
lean_ctor_set(x_441, 10, x_439);
lean_ctor_set(x_441, 11, x_440);
x_442 = lean_st_ref_set(x_3, x_441, x_427);
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_346 = x_421;
x_347 = x_443;
goto block_411;
}
else
{
uint8_t x_444; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_420);
if (x_444 == 0)
{
return x_420;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_420, 0);
x_446 = lean_ctor_get(x_420, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_420);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
lean_object* x_448; 
lean_dec(x_344);
x_448 = lean_ctor_get(x_419, 0);
lean_inc(x_448);
lean_dec(x_419);
x_346 = x_448;
x_347 = x_417;
goto block_411;
}
}
}
case 6:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_530; uint8_t x_568; 
x_456 = lean_ctor_get(x_1, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_1, 2);
lean_inc(x_457);
x_568 = l_Lean_Expr_hasLevelParam(x_456);
if (x_568 == 0)
{
uint8_t x_569; 
x_569 = l_Lean_Expr_hasFVar(x_456);
if (x_569 == 0)
{
uint8_t x_570; 
x_570 = l_Lean_Expr_hasMVar(x_456);
if (x_570 == 0)
{
x_458 = x_456;
x_459 = x_8;
goto block_529;
}
else
{
lean_object* x_571; 
x_571 = lean_box(0);
x_530 = x_571;
goto block_567;
}
}
else
{
lean_object* x_572; 
x_572 = lean_box(0);
x_530 = x_572;
goto block_567;
}
}
else
{
lean_object* x_573; 
x_573 = lean_box(0);
x_530 = x_573;
goto block_567;
}
block_529:
{
lean_object* x_460; lean_object* x_461; lean_object* x_485; uint8_t x_523; 
x_523 = l_Lean_Expr_hasLevelParam(x_457);
if (x_523 == 0)
{
uint8_t x_524; 
x_524 = l_Lean_Expr_hasFVar(x_457);
if (x_524 == 0)
{
uint8_t x_525; 
x_525 = l_Lean_Expr_hasMVar(x_457);
if (x_525 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_460 = x_457;
x_461 = x_459;
goto block_484;
}
else
{
lean_object* x_526; 
x_526 = lean_box(0);
x_485 = x_526;
goto block_522;
}
}
else
{
lean_object* x_527; 
x_527 = lean_box(0);
x_485 = x_527;
goto block_522;
}
}
else
{
lean_object* x_528; 
x_528 = lean_box(0);
x_485 = x_528;
goto block_522;
}
block_484:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; size_t x_467; size_t x_468; uint8_t x_469; 
x_462 = lean_ctor_get(x_1, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_1, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_1, 2);
lean_inc(x_464);
x_465 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
x_466 = l_Lean_Expr_lam___override(x_462, x_463, x_464, x_465);
x_467 = lean_ptr_addr(x_463);
lean_dec(x_463);
x_468 = lean_ptr_addr(x_458);
x_469 = lean_usize_dec_eq(x_467, x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_466);
lean_dec(x_464);
x_470 = l_Lean_Expr_lam___override(x_462, x_458, x_460, x_465);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_461);
return x_471;
}
else
{
size_t x_472; size_t x_473; uint8_t x_474; 
x_472 = lean_ptr_addr(x_464);
lean_dec(x_464);
x_473 = lean_ptr_addr(x_460);
x_474 = lean_usize_dec_eq(x_472, x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_466);
x_475 = l_Lean_Expr_lam___override(x_462, x_458, x_460, x_465);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_461);
return x_476;
}
else
{
uint8_t x_477; 
x_477 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_465, x_465);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_466);
x_478 = l_Lean_Expr_lam___override(x_462, x_458, x_460, x_465);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_461);
return x_479;
}
else
{
lean_object* x_480; 
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_458);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_466);
lean_ctor_set(x_480, 1, x_461);
return x_480;
}
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_1);
x_481 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_482 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_481);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_461);
return x_483;
}
}
block_522:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_485);
x_486 = lean_st_ref_get(x_7, x_459);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_st_ref_get(x_3, x_487);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
lean_inc(x_457);
x_492 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_491, x_457);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; 
lean_inc(x_7);
lean_inc(x_457);
x_493 = l_Lean_Meta_Closure_collectExprAux(x_457, x_2, x_3, x_4, x_5, x_6, x_7, x_490);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_st_ref_get(x_7, x_495);
lean_dec(x_7);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_498 = lean_st_ref_take(x_3, x_497);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_ctor_get(x_499, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
lean_inc(x_494);
x_503 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_502, x_457, x_494);
x_504 = lean_ctor_get(x_499, 2);
lean_inc(x_504);
x_505 = lean_ctor_get(x_499, 3);
lean_inc(x_505);
x_506 = lean_ctor_get(x_499, 4);
lean_inc(x_506);
x_507 = lean_ctor_get(x_499, 5);
lean_inc(x_507);
x_508 = lean_ctor_get(x_499, 6);
lean_inc(x_508);
x_509 = lean_ctor_get(x_499, 7);
lean_inc(x_509);
x_510 = lean_ctor_get(x_499, 8);
lean_inc(x_510);
x_511 = lean_ctor_get(x_499, 9);
lean_inc(x_511);
x_512 = lean_ctor_get(x_499, 10);
lean_inc(x_512);
x_513 = lean_ctor_get(x_499, 11);
lean_inc(x_513);
lean_dec(x_499);
x_514 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_514, 0, x_501);
lean_ctor_set(x_514, 1, x_503);
lean_ctor_set(x_514, 2, x_504);
lean_ctor_set(x_514, 3, x_505);
lean_ctor_set(x_514, 4, x_506);
lean_ctor_set(x_514, 5, x_507);
lean_ctor_set(x_514, 6, x_508);
lean_ctor_set(x_514, 7, x_509);
lean_ctor_set(x_514, 8, x_510);
lean_ctor_set(x_514, 9, x_511);
lean_ctor_set(x_514, 10, x_512);
lean_ctor_set(x_514, 11, x_513);
x_515 = lean_st_ref_set(x_3, x_514, x_500);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_460 = x_494;
x_461 = x_516;
goto block_484;
}
else
{
uint8_t x_517; 
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_7);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_493);
if (x_517 == 0)
{
return x_493;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_493, 0);
x_519 = lean_ctor_get(x_493, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_493);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
else
{
lean_object* x_521; 
lean_dec(x_457);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_521 = lean_ctor_get(x_492, 0);
lean_inc(x_521);
lean_dec(x_492);
x_460 = x_521;
x_461 = x_490;
goto block_484;
}
}
}
block_567:
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_530);
x_531 = lean_st_ref_get(x_7, x_8);
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec(x_531);
x_533 = lean_st_ref_get(x_3, x_532);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
lean_inc(x_456);
x_537 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_536, x_456);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_456);
x_538 = l_Lean_Meta_Closure_collectExprAux(x_456, x_2, x_3, x_4, x_5, x_6, x_7, x_535);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_st_ref_get(x_7, x_540);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec(x_541);
x_543 = lean_st_ref_take(x_3, x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_ctor_get(x_544, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
lean_inc(x_539);
x_548 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_547, x_456, x_539);
x_549 = lean_ctor_get(x_544, 2);
lean_inc(x_549);
x_550 = lean_ctor_get(x_544, 3);
lean_inc(x_550);
x_551 = lean_ctor_get(x_544, 4);
lean_inc(x_551);
x_552 = lean_ctor_get(x_544, 5);
lean_inc(x_552);
x_553 = lean_ctor_get(x_544, 6);
lean_inc(x_553);
x_554 = lean_ctor_get(x_544, 7);
lean_inc(x_554);
x_555 = lean_ctor_get(x_544, 8);
lean_inc(x_555);
x_556 = lean_ctor_get(x_544, 9);
lean_inc(x_556);
x_557 = lean_ctor_get(x_544, 10);
lean_inc(x_557);
x_558 = lean_ctor_get(x_544, 11);
lean_inc(x_558);
lean_dec(x_544);
x_559 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_559, 0, x_546);
lean_ctor_set(x_559, 1, x_548);
lean_ctor_set(x_559, 2, x_549);
lean_ctor_set(x_559, 3, x_550);
lean_ctor_set(x_559, 4, x_551);
lean_ctor_set(x_559, 5, x_552);
lean_ctor_set(x_559, 6, x_553);
lean_ctor_set(x_559, 7, x_554);
lean_ctor_set(x_559, 8, x_555);
lean_ctor_set(x_559, 9, x_556);
lean_ctor_set(x_559, 10, x_557);
lean_ctor_set(x_559, 11, x_558);
x_560 = lean_st_ref_set(x_3, x_559, x_545);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_458 = x_539;
x_459 = x_561;
goto block_529;
}
else
{
uint8_t x_562; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_562 = !lean_is_exclusive(x_538);
if (x_562 == 0)
{
return x_538;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_538, 0);
x_564 = lean_ctor_get(x_538, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_538);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
lean_object* x_566; 
lean_dec(x_456);
x_566 = lean_ctor_get(x_537, 0);
lean_inc(x_566);
lean_dec(x_537);
x_458 = x_566;
x_459 = x_535;
goto block_529;
}
}
}
case 7:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_648; uint8_t x_686; 
x_574 = lean_ctor_get(x_1, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_1, 2);
lean_inc(x_575);
x_686 = l_Lean_Expr_hasLevelParam(x_574);
if (x_686 == 0)
{
uint8_t x_687; 
x_687 = l_Lean_Expr_hasFVar(x_574);
if (x_687 == 0)
{
uint8_t x_688; 
x_688 = l_Lean_Expr_hasMVar(x_574);
if (x_688 == 0)
{
x_576 = x_574;
x_577 = x_8;
goto block_647;
}
else
{
lean_object* x_689; 
x_689 = lean_box(0);
x_648 = x_689;
goto block_685;
}
}
else
{
lean_object* x_690; 
x_690 = lean_box(0);
x_648 = x_690;
goto block_685;
}
}
else
{
lean_object* x_691; 
x_691 = lean_box(0);
x_648 = x_691;
goto block_685;
}
block_647:
{
lean_object* x_578; lean_object* x_579; lean_object* x_603; uint8_t x_641; 
x_641 = l_Lean_Expr_hasLevelParam(x_575);
if (x_641 == 0)
{
uint8_t x_642; 
x_642 = l_Lean_Expr_hasFVar(x_575);
if (x_642 == 0)
{
uint8_t x_643; 
x_643 = l_Lean_Expr_hasMVar(x_575);
if (x_643 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_578 = x_575;
x_579 = x_577;
goto block_602;
}
else
{
lean_object* x_644; 
x_644 = lean_box(0);
x_603 = x_644;
goto block_640;
}
}
else
{
lean_object* x_645; 
x_645 = lean_box(0);
x_603 = x_645;
goto block_640;
}
}
else
{
lean_object* x_646; 
x_646 = lean_box(0);
x_603 = x_646;
goto block_640;
}
block_602:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; size_t x_585; size_t x_586; uint8_t x_587; 
x_580 = lean_ctor_get(x_1, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_1, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_1, 2);
lean_inc(x_582);
x_583 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_584 = l_Lean_Expr_forallE___override(x_580, x_581, x_582, x_583);
x_585 = lean_ptr_addr(x_581);
lean_dec(x_581);
x_586 = lean_ptr_addr(x_576);
x_587 = lean_usize_dec_eq(x_585, x_586);
if (x_587 == 0)
{
lean_object* x_588; lean_object* x_589; 
lean_dec(x_584);
lean_dec(x_582);
x_588 = l_Lean_Expr_forallE___override(x_580, x_576, x_578, x_583);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_579);
return x_589;
}
else
{
size_t x_590; size_t x_591; uint8_t x_592; 
x_590 = lean_ptr_addr(x_582);
lean_dec(x_582);
x_591 = lean_ptr_addr(x_578);
x_592 = lean_usize_dec_eq(x_590, x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_584);
x_593 = l_Lean_Expr_forallE___override(x_580, x_576, x_578, x_583);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_579);
return x_594;
}
else
{
uint8_t x_595; 
x_595 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_583, x_583);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
lean_dec(x_584);
x_596 = l_Lean_Expr_forallE___override(x_580, x_576, x_578, x_583);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_579);
return x_597;
}
else
{
lean_object* x_598; 
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_576);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_584);
lean_ctor_set(x_598, 1, x_579);
return x_598;
}
}
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_1);
x_599 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_600 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_599);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_600);
lean_ctor_set(x_601, 1, x_579);
return x_601;
}
}
block_640:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_603);
x_604 = lean_st_ref_get(x_7, x_577);
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
lean_dec(x_604);
x_606 = lean_st_ref_get(x_3, x_605);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
lean_inc(x_575);
x_610 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_609, x_575);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; 
lean_inc(x_7);
lean_inc(x_575);
x_611 = l_Lean_Meta_Closure_collectExprAux(x_575, x_2, x_3, x_4, x_5, x_6, x_7, x_608);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_st_ref_get(x_7, x_613);
lean_dec(x_7);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_st_ref_take(x_3, x_615);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_inc(x_612);
x_621 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_620, x_575, x_612);
x_622 = lean_ctor_get(x_617, 2);
lean_inc(x_622);
x_623 = lean_ctor_get(x_617, 3);
lean_inc(x_623);
x_624 = lean_ctor_get(x_617, 4);
lean_inc(x_624);
x_625 = lean_ctor_get(x_617, 5);
lean_inc(x_625);
x_626 = lean_ctor_get(x_617, 6);
lean_inc(x_626);
x_627 = lean_ctor_get(x_617, 7);
lean_inc(x_627);
x_628 = lean_ctor_get(x_617, 8);
lean_inc(x_628);
x_629 = lean_ctor_get(x_617, 9);
lean_inc(x_629);
x_630 = lean_ctor_get(x_617, 10);
lean_inc(x_630);
x_631 = lean_ctor_get(x_617, 11);
lean_inc(x_631);
lean_dec(x_617);
x_632 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_632, 0, x_619);
lean_ctor_set(x_632, 1, x_621);
lean_ctor_set(x_632, 2, x_622);
lean_ctor_set(x_632, 3, x_623);
lean_ctor_set(x_632, 4, x_624);
lean_ctor_set(x_632, 5, x_625);
lean_ctor_set(x_632, 6, x_626);
lean_ctor_set(x_632, 7, x_627);
lean_ctor_set(x_632, 8, x_628);
lean_ctor_set(x_632, 9, x_629);
lean_ctor_set(x_632, 10, x_630);
lean_ctor_set(x_632, 11, x_631);
x_633 = lean_st_ref_set(x_3, x_632, x_618);
x_634 = lean_ctor_get(x_633, 1);
lean_inc(x_634);
lean_dec(x_633);
x_578 = x_612;
x_579 = x_634;
goto block_602;
}
else
{
uint8_t x_635; 
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_7);
lean_dec(x_1);
x_635 = !lean_is_exclusive(x_611);
if (x_635 == 0)
{
return x_611;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_611, 0);
x_637 = lean_ctor_get(x_611, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_611);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
else
{
lean_object* x_639; 
lean_dec(x_575);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_639 = lean_ctor_get(x_610, 0);
lean_inc(x_639);
lean_dec(x_610);
x_578 = x_639;
x_579 = x_608;
goto block_602;
}
}
}
block_685:
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_648);
x_649 = lean_st_ref_get(x_7, x_8);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
lean_dec(x_649);
x_651 = lean_st_ref_get(x_3, x_650);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
lean_inc(x_574);
x_655 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_654, x_574);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_574);
x_656 = l_Lean_Meta_Closure_collectExprAux(x_574, x_2, x_3, x_4, x_5, x_6, x_7, x_653);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = lean_st_ref_get(x_7, x_658);
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_661 = lean_st_ref_take(x_3, x_660);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_ctor_get(x_662, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_662, 1);
lean_inc(x_665);
lean_inc(x_657);
x_666 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_665, x_574, x_657);
x_667 = lean_ctor_get(x_662, 2);
lean_inc(x_667);
x_668 = lean_ctor_get(x_662, 3);
lean_inc(x_668);
x_669 = lean_ctor_get(x_662, 4);
lean_inc(x_669);
x_670 = lean_ctor_get(x_662, 5);
lean_inc(x_670);
x_671 = lean_ctor_get(x_662, 6);
lean_inc(x_671);
x_672 = lean_ctor_get(x_662, 7);
lean_inc(x_672);
x_673 = lean_ctor_get(x_662, 8);
lean_inc(x_673);
x_674 = lean_ctor_get(x_662, 9);
lean_inc(x_674);
x_675 = lean_ctor_get(x_662, 10);
lean_inc(x_675);
x_676 = lean_ctor_get(x_662, 11);
lean_inc(x_676);
lean_dec(x_662);
x_677 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_677, 0, x_664);
lean_ctor_set(x_677, 1, x_666);
lean_ctor_set(x_677, 2, x_667);
lean_ctor_set(x_677, 3, x_668);
lean_ctor_set(x_677, 4, x_669);
lean_ctor_set(x_677, 5, x_670);
lean_ctor_set(x_677, 6, x_671);
lean_ctor_set(x_677, 7, x_672);
lean_ctor_set(x_677, 8, x_673);
lean_ctor_set(x_677, 9, x_674);
lean_ctor_set(x_677, 10, x_675);
lean_ctor_set(x_677, 11, x_676);
x_678 = lean_st_ref_set(x_3, x_677, x_663);
x_679 = lean_ctor_get(x_678, 1);
lean_inc(x_679);
lean_dec(x_678);
x_576 = x_657;
x_577 = x_679;
goto block_647;
}
else
{
uint8_t x_680; 
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_680 = !lean_is_exclusive(x_656);
if (x_680 == 0)
{
return x_656;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_656, 0);
x_682 = lean_ctor_get(x_656, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_656);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
return x_683;
}
}
}
else
{
lean_object* x_684; 
lean_dec(x_574);
x_684 = lean_ctor_get(x_655, 0);
lean_inc(x_684);
lean_dec(x_655);
x_576 = x_684;
x_577 = x_653;
goto block_647;
}
}
}
case 8:
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_816; uint8_t x_854; 
x_692 = lean_ctor_get(x_1, 1);
lean_inc(x_692);
x_693 = lean_ctor_get(x_1, 2);
lean_inc(x_693);
x_694 = lean_ctor_get(x_1, 3);
lean_inc(x_694);
x_854 = l_Lean_Expr_hasLevelParam(x_692);
if (x_854 == 0)
{
uint8_t x_855; 
x_855 = l_Lean_Expr_hasFVar(x_692);
if (x_855 == 0)
{
uint8_t x_856; 
x_856 = l_Lean_Expr_hasMVar(x_692);
if (x_856 == 0)
{
x_695 = x_692;
x_696 = x_8;
goto block_815;
}
else
{
lean_object* x_857; 
x_857 = lean_box(0);
x_816 = x_857;
goto block_853;
}
}
else
{
lean_object* x_858; 
x_858 = lean_box(0);
x_816 = x_858;
goto block_853;
}
}
else
{
lean_object* x_859; 
x_859 = lean_box(0);
x_816 = x_859;
goto block_853;
}
block_815:
{
lean_object* x_697; lean_object* x_698; lean_object* x_771; uint8_t x_809; 
x_809 = l_Lean_Expr_hasLevelParam(x_693);
if (x_809 == 0)
{
uint8_t x_810; 
x_810 = l_Lean_Expr_hasFVar(x_693);
if (x_810 == 0)
{
uint8_t x_811; 
x_811 = l_Lean_Expr_hasMVar(x_693);
if (x_811 == 0)
{
x_697 = x_693;
x_698 = x_696;
goto block_770;
}
else
{
lean_object* x_812; 
x_812 = lean_box(0);
x_771 = x_812;
goto block_808;
}
}
else
{
lean_object* x_813; 
x_813 = lean_box(0);
x_771 = x_813;
goto block_808;
}
}
else
{
lean_object* x_814; 
x_814 = lean_box(0);
x_771 = x_814;
goto block_808;
}
block_770:
{
lean_object* x_699; lean_object* x_700; lean_object* x_726; uint8_t x_764; 
x_764 = l_Lean_Expr_hasLevelParam(x_694);
if (x_764 == 0)
{
uint8_t x_765; 
x_765 = l_Lean_Expr_hasFVar(x_694);
if (x_765 == 0)
{
uint8_t x_766; 
x_766 = l_Lean_Expr_hasMVar(x_694);
if (x_766 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_699 = x_694;
x_700 = x_698;
goto block_725;
}
else
{
lean_object* x_767; 
x_767 = lean_box(0);
x_726 = x_767;
goto block_763;
}
}
else
{
lean_object* x_768; 
x_768 = lean_box(0);
x_726 = x_768;
goto block_763;
}
}
else
{
lean_object* x_769; 
x_769 = lean_box(0);
x_726 = x_769;
goto block_763;
}
block_725:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; size_t x_706; size_t x_707; uint8_t x_708; 
x_701 = lean_ctor_get(x_1, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_1, 1);
lean_inc(x_702);
x_703 = lean_ctor_get(x_1, 2);
lean_inc(x_703);
x_704 = lean_ctor_get(x_1, 3);
lean_inc(x_704);
x_705 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_706 = lean_ptr_addr(x_702);
lean_dec(x_702);
x_707 = lean_ptr_addr(x_695);
x_708 = lean_usize_dec_eq(x_706, x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_1);
x_709 = l_Lean_Expr_letE___override(x_701, x_695, x_697, x_699, x_705);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_700);
return x_710;
}
else
{
size_t x_711; size_t x_712; uint8_t x_713; 
x_711 = lean_ptr_addr(x_703);
lean_dec(x_703);
x_712 = lean_ptr_addr(x_697);
x_713 = lean_usize_dec_eq(x_711, x_712);
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_704);
lean_dec(x_1);
x_714 = l_Lean_Expr_letE___override(x_701, x_695, x_697, x_699, x_705);
x_715 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_700);
return x_715;
}
else
{
size_t x_716; size_t x_717; uint8_t x_718; 
x_716 = lean_ptr_addr(x_704);
lean_dec(x_704);
x_717 = lean_ptr_addr(x_699);
x_718 = lean_usize_dec_eq(x_716, x_717);
if (x_718 == 0)
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_1);
x_719 = l_Lean_Expr_letE___override(x_701, x_695, x_697, x_699, x_705);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_700);
return x_720;
}
else
{
lean_object* x_721; 
lean_dec(x_701);
lean_dec(x_699);
lean_dec(x_697);
lean_dec(x_695);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_1);
lean_ctor_set(x_721, 1, x_700);
return x_721;
}
}
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_699);
lean_dec(x_697);
lean_dec(x_695);
lean_dec(x_1);
x_722 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_723 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_722);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_700);
return x_724;
}
}
block_763:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_726);
x_727 = lean_st_ref_get(x_7, x_698);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
lean_dec(x_727);
x_729 = lean_st_ref_get(x_3, x_728);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
lean_inc(x_694);
x_733 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_732, x_694);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; 
lean_inc(x_7);
lean_inc(x_694);
x_734 = l_Lean_Meta_Closure_collectExprAux(x_694, x_2, x_3, x_4, x_5, x_6, x_7, x_731);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_st_ref_get(x_7, x_736);
lean_dec(x_7);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
x_739 = lean_st_ref_take(x_3, x_738);
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = lean_ctor_get(x_740, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_740, 1);
lean_inc(x_743);
lean_inc(x_735);
x_744 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_743, x_694, x_735);
x_745 = lean_ctor_get(x_740, 2);
lean_inc(x_745);
x_746 = lean_ctor_get(x_740, 3);
lean_inc(x_746);
x_747 = lean_ctor_get(x_740, 4);
lean_inc(x_747);
x_748 = lean_ctor_get(x_740, 5);
lean_inc(x_748);
x_749 = lean_ctor_get(x_740, 6);
lean_inc(x_749);
x_750 = lean_ctor_get(x_740, 7);
lean_inc(x_750);
x_751 = lean_ctor_get(x_740, 8);
lean_inc(x_751);
x_752 = lean_ctor_get(x_740, 9);
lean_inc(x_752);
x_753 = lean_ctor_get(x_740, 10);
lean_inc(x_753);
x_754 = lean_ctor_get(x_740, 11);
lean_inc(x_754);
lean_dec(x_740);
x_755 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_755, 0, x_742);
lean_ctor_set(x_755, 1, x_744);
lean_ctor_set(x_755, 2, x_745);
lean_ctor_set(x_755, 3, x_746);
lean_ctor_set(x_755, 4, x_747);
lean_ctor_set(x_755, 5, x_748);
lean_ctor_set(x_755, 6, x_749);
lean_ctor_set(x_755, 7, x_750);
lean_ctor_set(x_755, 8, x_751);
lean_ctor_set(x_755, 9, x_752);
lean_ctor_set(x_755, 10, x_753);
lean_ctor_set(x_755, 11, x_754);
x_756 = lean_st_ref_set(x_3, x_755, x_741);
x_757 = lean_ctor_get(x_756, 1);
lean_inc(x_757);
lean_dec(x_756);
x_699 = x_735;
x_700 = x_757;
goto block_725;
}
else
{
uint8_t x_758; 
lean_dec(x_697);
lean_dec(x_695);
lean_dec(x_694);
lean_dec(x_7);
lean_dec(x_1);
x_758 = !lean_is_exclusive(x_734);
if (x_758 == 0)
{
return x_734;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_734, 0);
x_760 = lean_ctor_get(x_734, 1);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_734);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
return x_761;
}
}
}
else
{
lean_object* x_762; 
lean_dec(x_694);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_762 = lean_ctor_get(x_733, 0);
lean_inc(x_762);
lean_dec(x_733);
x_699 = x_762;
x_700 = x_731;
goto block_725;
}
}
}
block_808:
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_771);
x_772 = lean_st_ref_get(x_7, x_696);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
lean_dec(x_772);
x_774 = lean_st_ref_get(x_3, x_773);
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
lean_inc(x_693);
x_778 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_777, x_693);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_693);
x_779 = l_Lean_Meta_Closure_collectExprAux(x_693, x_2, x_3, x_4, x_5, x_6, x_7, x_776);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
lean_dec(x_779);
x_782 = lean_st_ref_get(x_7, x_781);
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
lean_dec(x_782);
x_784 = lean_st_ref_take(x_3, x_783);
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = lean_ctor_get(x_785, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_inc(x_780);
x_789 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_788, x_693, x_780);
x_790 = lean_ctor_get(x_785, 2);
lean_inc(x_790);
x_791 = lean_ctor_get(x_785, 3);
lean_inc(x_791);
x_792 = lean_ctor_get(x_785, 4);
lean_inc(x_792);
x_793 = lean_ctor_get(x_785, 5);
lean_inc(x_793);
x_794 = lean_ctor_get(x_785, 6);
lean_inc(x_794);
x_795 = lean_ctor_get(x_785, 7);
lean_inc(x_795);
x_796 = lean_ctor_get(x_785, 8);
lean_inc(x_796);
x_797 = lean_ctor_get(x_785, 9);
lean_inc(x_797);
x_798 = lean_ctor_get(x_785, 10);
lean_inc(x_798);
x_799 = lean_ctor_get(x_785, 11);
lean_inc(x_799);
lean_dec(x_785);
x_800 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_800, 0, x_787);
lean_ctor_set(x_800, 1, x_789);
lean_ctor_set(x_800, 2, x_790);
lean_ctor_set(x_800, 3, x_791);
lean_ctor_set(x_800, 4, x_792);
lean_ctor_set(x_800, 5, x_793);
lean_ctor_set(x_800, 6, x_794);
lean_ctor_set(x_800, 7, x_795);
lean_ctor_set(x_800, 8, x_796);
lean_ctor_set(x_800, 9, x_797);
lean_ctor_set(x_800, 10, x_798);
lean_ctor_set(x_800, 11, x_799);
x_801 = lean_st_ref_set(x_3, x_800, x_786);
x_802 = lean_ctor_get(x_801, 1);
lean_inc(x_802);
lean_dec(x_801);
x_697 = x_780;
x_698 = x_802;
goto block_770;
}
else
{
uint8_t x_803; 
lean_dec(x_695);
lean_dec(x_694);
lean_dec(x_693);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_779);
if (x_803 == 0)
{
return x_779;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_779, 0);
x_805 = lean_ctor_get(x_779, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_779);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
else
{
lean_object* x_807; 
lean_dec(x_693);
x_807 = lean_ctor_get(x_778, 0);
lean_inc(x_807);
lean_dec(x_778);
x_697 = x_807;
x_698 = x_776;
goto block_770;
}
}
}
block_853:
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_816);
x_817 = lean_st_ref_get(x_7, x_8);
x_818 = lean_ctor_get(x_817, 1);
lean_inc(x_818);
lean_dec(x_817);
x_819 = lean_st_ref_get(x_3, x_818);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
lean_inc(x_692);
x_823 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_822, x_692);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_692);
x_824 = l_Lean_Meta_Closure_collectExprAux(x_692, x_2, x_3, x_4, x_5, x_6, x_7, x_821);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_827 = lean_st_ref_get(x_7, x_826);
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
lean_dec(x_827);
x_829 = lean_st_ref_take(x_3, x_828);
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = lean_ctor_get(x_830, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_inc(x_825);
x_834 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_833, x_692, x_825);
x_835 = lean_ctor_get(x_830, 2);
lean_inc(x_835);
x_836 = lean_ctor_get(x_830, 3);
lean_inc(x_836);
x_837 = lean_ctor_get(x_830, 4);
lean_inc(x_837);
x_838 = lean_ctor_get(x_830, 5);
lean_inc(x_838);
x_839 = lean_ctor_get(x_830, 6);
lean_inc(x_839);
x_840 = lean_ctor_get(x_830, 7);
lean_inc(x_840);
x_841 = lean_ctor_get(x_830, 8);
lean_inc(x_841);
x_842 = lean_ctor_get(x_830, 9);
lean_inc(x_842);
x_843 = lean_ctor_get(x_830, 10);
lean_inc(x_843);
x_844 = lean_ctor_get(x_830, 11);
lean_inc(x_844);
lean_dec(x_830);
x_845 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_845, 0, x_832);
lean_ctor_set(x_845, 1, x_834);
lean_ctor_set(x_845, 2, x_835);
lean_ctor_set(x_845, 3, x_836);
lean_ctor_set(x_845, 4, x_837);
lean_ctor_set(x_845, 5, x_838);
lean_ctor_set(x_845, 6, x_839);
lean_ctor_set(x_845, 7, x_840);
lean_ctor_set(x_845, 8, x_841);
lean_ctor_set(x_845, 9, x_842);
lean_ctor_set(x_845, 10, x_843);
lean_ctor_set(x_845, 11, x_844);
x_846 = lean_st_ref_set(x_3, x_845, x_831);
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
lean_dec(x_846);
x_695 = x_825;
x_696 = x_847;
goto block_815;
}
else
{
uint8_t x_848; 
lean_dec(x_694);
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_848 = !lean_is_exclusive(x_824);
if (x_848 == 0)
{
return x_824;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_824, 0);
x_850 = lean_ctor_get(x_824, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_824);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
return x_851;
}
}
}
else
{
lean_object* x_852; 
lean_dec(x_692);
x_852 = lean_ctor_get(x_823, 0);
lean_inc(x_852);
lean_dec(x_823);
x_695 = x_852;
x_696 = x_821;
goto block_815;
}
}
}
case 10:
{
lean_object* x_860; lean_object* x_861; uint8_t x_899; 
x_860 = lean_ctor_get(x_1, 1);
lean_inc(x_860);
x_899 = l_Lean_Expr_hasLevelParam(x_860);
if (x_899 == 0)
{
uint8_t x_900; 
x_900 = l_Lean_Expr_hasFVar(x_860);
if (x_900 == 0)
{
uint8_t x_901; 
x_901 = l_Lean_Expr_hasMVar(x_860);
if (x_901 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_860;
x_10 = x_8;
goto block_22;
}
else
{
lean_object* x_902; 
x_902 = lean_box(0);
x_861 = x_902;
goto block_898;
}
}
else
{
lean_object* x_903; 
x_903 = lean_box(0);
x_861 = x_903;
goto block_898;
}
}
else
{
lean_object* x_904; 
x_904 = lean_box(0);
x_861 = x_904;
goto block_898;
}
block_898:
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_861);
x_862 = lean_st_ref_get(x_7, x_8);
x_863 = lean_ctor_get(x_862, 1);
lean_inc(x_863);
lean_dec(x_862);
x_864 = lean_st_ref_get(x_3, x_863);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
lean_inc(x_860);
x_868 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_867, x_860);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; 
lean_inc(x_7);
lean_inc(x_860);
x_869 = l_Lean_Meta_Closure_collectExprAux(x_860, x_2, x_3, x_4, x_5, x_6, x_7, x_866);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_st_ref_get(x_7, x_871);
lean_dec(x_7);
x_873 = lean_ctor_get(x_872, 1);
lean_inc(x_873);
lean_dec(x_872);
x_874 = lean_st_ref_take(x_3, x_873);
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
lean_dec(x_874);
x_877 = lean_ctor_get(x_875, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_875, 1);
lean_inc(x_878);
lean_inc(x_870);
x_879 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_878, x_860, x_870);
x_880 = lean_ctor_get(x_875, 2);
lean_inc(x_880);
x_881 = lean_ctor_get(x_875, 3);
lean_inc(x_881);
x_882 = lean_ctor_get(x_875, 4);
lean_inc(x_882);
x_883 = lean_ctor_get(x_875, 5);
lean_inc(x_883);
x_884 = lean_ctor_get(x_875, 6);
lean_inc(x_884);
x_885 = lean_ctor_get(x_875, 7);
lean_inc(x_885);
x_886 = lean_ctor_get(x_875, 8);
lean_inc(x_886);
x_887 = lean_ctor_get(x_875, 9);
lean_inc(x_887);
x_888 = lean_ctor_get(x_875, 10);
lean_inc(x_888);
x_889 = lean_ctor_get(x_875, 11);
lean_inc(x_889);
lean_dec(x_875);
x_890 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_890, 0, x_877);
lean_ctor_set(x_890, 1, x_879);
lean_ctor_set(x_890, 2, x_880);
lean_ctor_set(x_890, 3, x_881);
lean_ctor_set(x_890, 4, x_882);
lean_ctor_set(x_890, 5, x_883);
lean_ctor_set(x_890, 6, x_884);
lean_ctor_set(x_890, 7, x_885);
lean_ctor_set(x_890, 8, x_886);
lean_ctor_set(x_890, 9, x_887);
lean_ctor_set(x_890, 10, x_888);
lean_ctor_set(x_890, 11, x_889);
x_891 = lean_st_ref_set(x_3, x_890, x_876);
x_892 = lean_ctor_get(x_891, 1);
lean_inc(x_892);
lean_dec(x_891);
x_9 = x_870;
x_10 = x_892;
goto block_22;
}
else
{
uint8_t x_893; 
lean_dec(x_860);
lean_dec(x_7);
lean_dec(x_1);
x_893 = !lean_is_exclusive(x_869);
if (x_893 == 0)
{
return x_869;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_869, 0);
x_895 = lean_ctor_get(x_869, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_869);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
}
else
{
lean_object* x_897; 
lean_dec(x_860);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_897 = lean_ctor_get(x_868, 0);
lean_inc(x_897);
lean_dec(x_868);
x_9 = x_897;
x_10 = x_866;
goto block_22;
}
}
}
case 11:
{
lean_object* x_905; lean_object* x_906; uint8_t x_944; 
x_905 = lean_ctor_get(x_1, 2);
lean_inc(x_905);
x_944 = l_Lean_Expr_hasLevelParam(x_905);
if (x_944 == 0)
{
uint8_t x_945; 
x_945 = l_Lean_Expr_hasFVar(x_905);
if (x_945 == 0)
{
uint8_t x_946; 
x_946 = l_Lean_Expr_hasMVar(x_905);
if (x_946 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = x_905;
x_24 = x_8;
goto block_37;
}
else
{
lean_object* x_947; 
x_947 = lean_box(0);
x_906 = x_947;
goto block_943;
}
}
else
{
lean_object* x_948; 
x_948 = lean_box(0);
x_906 = x_948;
goto block_943;
}
}
else
{
lean_object* x_949; 
x_949 = lean_box(0);
x_906 = x_949;
goto block_943;
}
block_943:
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_906);
x_907 = lean_st_ref_get(x_7, x_8);
x_908 = lean_ctor_get(x_907, 1);
lean_inc(x_908);
lean_dec(x_907);
x_909 = lean_st_ref_get(x_3, x_908);
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
lean_dec(x_909);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
lean_inc(x_905);
x_913 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_912, x_905);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; 
lean_inc(x_7);
lean_inc(x_905);
x_914 = l_Lean_Meta_Closure_collectExprAux(x_905, x_2, x_3, x_4, x_5, x_6, x_7, x_911);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = lean_st_ref_get(x_7, x_916);
lean_dec(x_7);
x_918 = lean_ctor_get(x_917, 1);
lean_inc(x_918);
lean_dec(x_917);
x_919 = lean_st_ref_take(x_3, x_918);
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_ctor_get(x_920, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_920, 1);
lean_inc(x_923);
lean_inc(x_915);
x_924 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_923, x_905, x_915);
x_925 = lean_ctor_get(x_920, 2);
lean_inc(x_925);
x_926 = lean_ctor_get(x_920, 3);
lean_inc(x_926);
x_927 = lean_ctor_get(x_920, 4);
lean_inc(x_927);
x_928 = lean_ctor_get(x_920, 5);
lean_inc(x_928);
x_929 = lean_ctor_get(x_920, 6);
lean_inc(x_929);
x_930 = lean_ctor_get(x_920, 7);
lean_inc(x_930);
x_931 = lean_ctor_get(x_920, 8);
lean_inc(x_931);
x_932 = lean_ctor_get(x_920, 9);
lean_inc(x_932);
x_933 = lean_ctor_get(x_920, 10);
lean_inc(x_933);
x_934 = lean_ctor_get(x_920, 11);
lean_inc(x_934);
lean_dec(x_920);
x_935 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_935, 0, x_922);
lean_ctor_set(x_935, 1, x_924);
lean_ctor_set(x_935, 2, x_925);
lean_ctor_set(x_935, 3, x_926);
lean_ctor_set(x_935, 4, x_927);
lean_ctor_set(x_935, 5, x_928);
lean_ctor_set(x_935, 6, x_929);
lean_ctor_set(x_935, 7, x_930);
lean_ctor_set(x_935, 8, x_931);
lean_ctor_set(x_935, 9, x_932);
lean_ctor_set(x_935, 10, x_933);
lean_ctor_set(x_935, 11, x_934);
x_936 = lean_st_ref_set(x_3, x_935, x_921);
x_937 = lean_ctor_get(x_936, 1);
lean_inc(x_937);
lean_dec(x_936);
x_23 = x_915;
x_24 = x_937;
goto block_37;
}
else
{
uint8_t x_938; 
lean_dec(x_905);
lean_dec(x_7);
lean_dec(x_1);
x_938 = !lean_is_exclusive(x_914);
if (x_938 == 0)
{
return x_914;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_914, 0);
x_940 = lean_ctor_get(x_914, 1);
lean_inc(x_940);
lean_inc(x_939);
lean_dec(x_914);
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
return x_941;
}
}
}
else
{
lean_object* x_942; 
lean_dec(x_905);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_942 = lean_ctor_get(x_913, 0);
lean_inc(x_942);
lean_dec(x_913);
x_23 = x_942;
x_24 = x_911;
goto block_37;
}
}
}
default: 
{
lean_object* x_950; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_950 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_950, 0, x_1);
lean_ctor_set(x_950, 1, x_8);
return x_950;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_99; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_99 = l_Lean_Expr_hasLevelParam(x_11);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_hasFVar(x_11);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_hasMVar(x_11);
if (x_101 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_102; 
lean_free_object(x_9);
x_102 = lean_box(0);
x_13 = x_102;
goto block_98;
}
}
else
{
lean_object* x_103; 
lean_free_object(x_9);
x_103 = lean_box(0);
x_13 = x_103;
goto block_98;
}
}
else
{
lean_object* x_104; 
lean_free_object(x_9);
x_104 = lean_box(0);
x_13 = x_104;
goto block_98;
}
block_98:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_7, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_3, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_11);
x_21 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_20, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_16);
lean_inc(x_7);
lean_inc(x_11);
x_22 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_23);
x_32 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_31, x_11, x_23);
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_3, x_28, x_29);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_23);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
x_40 = lean_ctor_get(x_28, 2);
x_41 = lean_ctor_get(x_28, 3);
x_42 = lean_ctor_get(x_28, 4);
x_43 = lean_ctor_get(x_28, 5);
x_44 = lean_ctor_get(x_28, 6);
x_45 = lean_ctor_get(x_28, 7);
x_46 = lean_ctor_get(x_28, 8);
x_47 = lean_ctor_get(x_28, 9);
x_48 = lean_ctor_get(x_28, 10);
x_49 = lean_ctor_get(x_28, 11);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
lean_inc(x_23);
x_50 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_39, x_11, x_23);
x_51 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_42);
lean_ctor_set(x_51, 5, x_43);
lean_ctor_set(x_51, 6, x_44);
lean_ctor_set(x_51, 7, x_45);
lean_ctor_set(x_51, 8, x_46);
lean_ctor_set(x_51, 9, x_47);
lean_ctor_set(x_51, 10, x_48);
lean_ctor_set(x_51, 11, x_49);
x_52 = lean_st_ref_set(x_3, x_51, x_29);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_23);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = lean_ctor_get(x_21, 0);
lean_inc(x_60);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_60);
return x_16;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_11);
x_64 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_63, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_inc(x_7);
lean_inc(x_11);
x_65 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_st_ref_get(x_7, x_67);
lean_dec(x_7);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_3, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 8);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 9);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 10);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 11);
lean_inc(x_84);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 lean_ctor_release(x_71, 6);
 lean_ctor_release(x_71, 7);
 lean_ctor_release(x_71, 8);
 lean_ctor_release(x_71, 9);
 lean_ctor_release(x_71, 10);
 lean_ctor_release(x_71, 11);
 x_85 = x_71;
} else {
 lean_dec_ref(x_71);
 x_85 = lean_box(0);
}
lean_inc(x_66);
x_86 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_74, x_11, x_66);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 12, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_75);
lean_ctor_set(x_87, 3, x_76);
lean_ctor_set(x_87, 4, x_77);
lean_ctor_set(x_87, 5, x_78);
lean_ctor_set(x_87, 6, x_79);
lean_ctor_set(x_87, 7, x_80);
lean_ctor_set(x_87, 8, x_81);
lean_ctor_set(x_87, 9, x_82);
lean_ctor_set(x_87, 10, x_83);
lean_ctor_set(x_87, 11, x_84);
x_88 = lean_st_ref_set(x_3, x_87, x_72);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_66);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_11);
lean_dec(x_7);
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_94 = x_65;
} else {
 lean_dec_ref(x_65);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = lean_ctor_get(x_64, 0);
lean_inc(x_96);
lean_dec(x_64);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_62);
return x_97;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_150; 
x_105 = lean_ctor_get(x_9, 0);
x_106 = lean_ctor_get(x_9, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_9);
x_150 = l_Lean_Expr_hasLevelParam(x_105);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasFVar(x_105);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = l_Lean_Expr_hasMVar(x_105);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_105);
lean_ctor_set(x_153, 1, x_106);
return x_153;
}
else
{
lean_object* x_154; 
x_154 = lean_box(0);
x_107 = x_154;
goto block_149;
}
}
else
{
lean_object* x_155; 
x_155 = lean_box(0);
x_107 = x_155;
goto block_149;
}
}
else
{
lean_object* x_156; 
x_156 = lean_box(0);
x_107 = x_156;
goto block_149;
}
block_149:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
x_108 = lean_st_ref_get(x_7, x_106);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_get(x_3, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
lean_inc(x_105);
x_115 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_114, x_105);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_inc(x_7);
lean_inc(x_105);
x_116 = l_Lean_Meta_Closure_collectExprAux(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_7, x_118);
lean_dec(x_7);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_take(x_3, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 7);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 8);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 9);
lean_inc(x_133);
x_134 = lean_ctor_get(x_122, 10);
lean_inc(x_134);
x_135 = lean_ctor_get(x_122, 11);
lean_inc(x_135);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 lean_ctor_release(x_122, 6);
 lean_ctor_release(x_122, 7);
 lean_ctor_release(x_122, 8);
 lean_ctor_release(x_122, 9);
 lean_ctor_release(x_122, 10);
 lean_ctor_release(x_122, 11);
 x_136 = x_122;
} else {
 lean_dec_ref(x_122);
 x_136 = lean_box(0);
}
lean_inc(x_117);
x_137 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_125, x_105, x_117);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 12, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_126);
lean_ctor_set(x_138, 3, x_127);
lean_ctor_set(x_138, 4, x_128);
lean_ctor_set(x_138, 5, x_129);
lean_ctor_set(x_138, 6, x_130);
lean_ctor_set(x_138, 7, x_131);
lean_ctor_set(x_138, 8, x_132);
lean_ctor_set(x_138, 9, x_133);
lean_ctor_set(x_138, 10, x_134);
lean_ctor_set(x_138, 11, x_135);
x_139 = lean_st_ref_set(x_3, x_138, x_123);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_117);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_105);
lean_dec(x_7);
x_143 = lean_ctor_get(x_116, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_145 = x_116;
} else {
 lean_dec_ref(x_116);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_105);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_147 = lean_ctor_get(x_115, 0);
lean_inc(x_147);
lean_dec(x_115);
if (lean_is_scalar(x_113)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_113;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_112);
return x_148;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = !lean_is_exclusive(x_9);
if (x_157 == 0)
{
return x_9;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_9, 0);
x_159 = lean_ctor_get(x_9, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_9);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 11);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_isEmpty___rarg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_10);
x_16 = lean_st_ref_get(x_5, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_19, 11);
x_23 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_24 = l_Array_back___rarg(x_23, x_22);
x_25 = lean_array_pop(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_26, x_25, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_19, 11, x_29);
x_31 = lean_st_ref_set(x_1, x_19, x_20);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
x_38 = lean_ctor_get(x_19, 2);
x_39 = lean_ctor_get(x_19, 3);
x_40 = lean_ctor_get(x_19, 4);
x_41 = lean_ctor_get(x_19, 5);
x_42 = lean_ctor_get(x_19, 6);
x_43 = lean_ctor_get(x_19, 7);
x_44 = lean_ctor_get(x_19, 8);
x_45 = lean_ctor_get(x_19, 9);
x_46 = lean_ctor_get(x_19, 10);
x_47 = lean_ctor_get(x_19, 11);
lean_inc(x_47);
lean_inc(x_46);
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
lean_dec(x_19);
x_48 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_49 = l_Array_back___rarg(x_48, x_47);
x_50 = lean_array_pop(x_47);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_51, x_50, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_39);
lean_ctor_set(x_56, 4, x_40);
lean_ctor_set(x_56, 5, x_41);
lean_ctor_set(x_56, 6, x_42);
lean_ctor_set(x_56, 7, x_43);
lean_ctor_set(x_56, 8, x_44);
lean_ctor_set(x_56, 9, x_45);
lean_ctor_set(x_56, 10, x_46);
lean_ctor_set(x_56, 11, x_54);
x_57 = lean_st_ref_set(x_1, x_56, x_20);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_7);
x_61 = lean_box(0);
lean_ctor_set(x_10, 0, x_61);
return x_10;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_ctor_get(x_62, 11);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Array_isEmpty___rarg(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_66 = lean_st_ref_get(x_5, x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_1, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_69, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_69, 9);
lean_inc(x_80);
x_81 = lean_ctor_get(x_69, 10);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 11);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 lean_ctor_release(x_69, 5);
 lean_ctor_release(x_69, 6);
 lean_ctor_release(x_69, 7);
 lean_ctor_release(x_69, 8);
 lean_ctor_release(x_69, 9);
 lean_ctor_release(x_69, 10);
 lean_ctor_release(x_69, 11);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_85 = l_Array_back___rarg(x_84, x_82);
x_86 = lean_array_pop(x_82);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_87, x_86, x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
if (lean_is_scalar(x_83)) {
 x_92 = lean_alloc_ctor(0, 12, 0);
} else {
 x_92 = x_83;
}
lean_ctor_set(x_92, 0, x_71);
lean_ctor_set(x_92, 1, x_72);
lean_ctor_set(x_92, 2, x_73);
lean_ctor_set(x_92, 3, x_74);
lean_ctor_set(x_92, 4, x_75);
lean_ctor_set(x_92, 5, x_76);
lean_ctor_set(x_92, 6, x_77);
lean_ctor_set(x_92, 7, x_78);
lean_ctor_set(x_92, 8, x_79);
lean_ctor_set(x_92, 9, x_80);
lean_ctor_set(x_92, 10, x_81);
lean_ctor_set(x_92, 11, x_90);
x_93 = lean_st_ref_set(x_1, x_92, x_70);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_7);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_63);
return x_98;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 10);
x_16 = lean_array_push(x_15, x_1);
lean_ctor_set(x_12, 10, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get(x_12, 7);
x_32 = lean_ctor_get(x_12, 8);
x_33 = lean_ctor_get(x_12, 9);
x_34 = lean_ctor_get(x_12, 10);
x_35 = lean_ctor_get(x_12, 11);
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
lean_dec(x_12);
x_36 = lean_array_push(x_34, x_1);
x_37 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
lean_ctor_set(x_37, 9, x_33);
lean_ctor_set(x_37, 10, x_36);
lean_ctor_set(x_37, 11, x_35);
x_38 = lean_st_ref_set(x_3, x_37, x_13);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
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
lean_inc(x_10);
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_18, 5);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_24, sizeof(void*)*4 + 1, x_23);
x_25 = lean_array_push(x_21, x_24);
lean_ctor_set(x_18, 5, x_25);
x_26 = lean_st_ref_set(x_6, x_18, x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 2);
x_36 = lean_ctor_get(x_18, 3);
x_37 = lean_ctor_get(x_18, 4);
x_38 = lean_ctor_get(x_18, 5);
x_39 = lean_ctor_get(x_18, 6);
x_40 = lean_ctor_get(x_18, 7);
x_41 = lean_ctor_get(x_18, 8);
x_42 = lean_ctor_get(x_18, 9);
x_43 = lean_ctor_get(x_18, 10);
x_44 = lean_ctor_get(x_18, 11);
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
lean_dec(x_18);
x_45 = lean_unsigned_to_nat(0u);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_13);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 1, x_46);
x_48 = lean_array_push(x_38, x_47);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_35);
lean_ctor_set(x_49, 3, x_36);
lean_ctor_set(x_49, 4, x_37);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_39);
lean_ctor_set(x_49, 7, x_40);
lean_ctor_set(x_49, 8, x_41);
lean_ctor_set(x_49, 9, x_42);
lean_ctor_set(x_49, 10, x_43);
lean_ctor_set(x_49, 11, x_44);
x_50 = lean_st_ref_set(x_6, x_49, x_19);
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
x_53 = lean_box(0);
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
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_2, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_70 = lean_ctor_get(x_67, 7);
x_71 = lean_unsigned_to_nat(0u);
x_72 = 0;
x_73 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_71);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_72);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_73);
x_74 = lean_array_push(x_70, x_21);
lean_ctor_set(x_67, 7, x_74);
x_75 = lean_st_ref_set(x_2, x_67, x_68);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_6, x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_take(x_2, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_80, 5);
x_84 = lean_array_get_size(x_83);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = 0;
x_87 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_85, x_86, x_83);
lean_dec(x_62);
lean_ctor_set(x_80, 5, x_87);
x_88 = lean_st_ref_set(x_2, x_80, x_81);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_7 = x_89;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
x_93 = lean_ctor_get(x_80, 2);
x_94 = lean_ctor_get(x_80, 3);
x_95 = lean_ctor_get(x_80, 4);
x_96 = lean_ctor_get(x_80, 5);
x_97 = lean_ctor_get(x_80, 6);
x_98 = lean_ctor_get(x_80, 7);
x_99 = lean_ctor_get(x_80, 8);
x_100 = lean_ctor_get(x_80, 9);
x_101 = lean_ctor_get(x_80, 10);
x_102 = lean_ctor_get(x_80, 11);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_103 = lean_array_get_size(x_96);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = 0;
x_106 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_104, x_105, x_96);
lean_dec(x_62);
x_107 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_92);
lean_ctor_set(x_107, 2, x_93);
lean_ctor_set(x_107, 3, x_94);
lean_ctor_set(x_107, 4, x_95);
lean_ctor_set(x_107, 5, x_106);
lean_ctor_set(x_107, 6, x_97);
lean_ctor_set(x_107, 7, x_98);
lean_ctor_set(x_107, 8, x_99);
lean_ctor_set(x_107, 9, x_100);
lean_ctor_set(x_107, 10, x_101);
lean_ctor_set(x_107, 11, x_102);
x_108 = lean_st_ref_set(x_2, x_107, x_81);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_7 = x_109;
goto _start;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_111 = lean_ctor_get(x_67, 0);
x_112 = lean_ctor_get(x_67, 1);
x_113 = lean_ctor_get(x_67, 2);
x_114 = lean_ctor_get(x_67, 3);
x_115 = lean_ctor_get(x_67, 4);
x_116 = lean_ctor_get(x_67, 5);
x_117 = lean_ctor_get(x_67, 6);
x_118 = lean_ctor_get(x_67, 7);
x_119 = lean_ctor_get(x_67, 8);
x_120 = lean_ctor_get(x_67, 9);
x_121 = lean_ctor_get(x_67, 10);
x_122 = lean_ctor_get(x_67, 11);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_67);
x_123 = lean_unsigned_to_nat(0u);
x_124 = 0;
x_125 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_123);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_124);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_125);
x_126 = lean_array_push(x_118, x_21);
x_127 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_127, 0, x_111);
lean_ctor_set(x_127, 1, x_112);
lean_ctor_set(x_127, 2, x_113);
lean_ctor_set(x_127, 3, x_114);
lean_ctor_set(x_127, 4, x_115);
lean_ctor_set(x_127, 5, x_116);
lean_ctor_set(x_127, 6, x_117);
lean_ctor_set(x_127, 7, x_126);
lean_ctor_set(x_127, 8, x_119);
lean_ctor_set(x_127, 9, x_120);
lean_ctor_set(x_127, 10, x_121);
lean_ctor_set(x_127, 11, x_122);
x_128 = lean_st_ref_set(x_2, x_127, x_68);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_get(x_6, x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_take(x_2, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 7);
lean_inc(x_142);
x_143 = lean_ctor_get(x_133, 8);
lean_inc(x_143);
x_144 = lean_ctor_get(x_133, 9);
lean_inc(x_144);
x_145 = lean_ctor_get(x_133, 10);
lean_inc(x_145);
x_146 = lean_ctor_get(x_133, 11);
lean_inc(x_146);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 lean_ctor_release(x_133, 6);
 lean_ctor_release(x_133, 7);
 lean_ctor_release(x_133, 8);
 lean_ctor_release(x_133, 9);
 lean_ctor_release(x_133, 10);
 lean_ctor_release(x_133, 11);
 x_147 = x_133;
} else {
 lean_dec_ref(x_133);
 x_147 = lean_box(0);
}
x_148 = lean_array_get_size(x_140);
x_149 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_150 = 0;
x_151 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_149, x_150, x_140);
lean_dec(x_62);
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(0, 12, 0);
} else {
 x_152 = x_147;
}
lean_ctor_set(x_152, 0, x_135);
lean_ctor_set(x_152, 1, x_136);
lean_ctor_set(x_152, 2, x_137);
lean_ctor_set(x_152, 3, x_138);
lean_ctor_set(x_152, 4, x_139);
lean_ctor_set(x_152, 5, x_151);
lean_ctor_set(x_152, 6, x_141);
lean_ctor_set(x_152, 7, x_142);
lean_ctor_set(x_152, 8, x_143);
lean_ctor_set(x_152, 9, x_144);
lean_ctor_set(x_152, 10, x_145);
lean_ctor_set(x_152, 11, x_146);
x_153 = lean_st_ref_set(x_2, x_152, x_134);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_7 = x_154;
goto _start;
}
}
else
{
uint8_t x_156; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_61);
if (x_156 == 0)
{
return x_61;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_61, 0);
x_158 = lean_ctor_get(x_61, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_61);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_58);
if (x_160 == 0)
{
return x_58;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_58, 0);
x_162 = lean_ctor_get(x_58, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_58);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_21, 2);
x_165 = lean_ctor_get(x_21, 3);
x_166 = lean_ctor_get(x_21, 4);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_21);
x_167 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_168, x_18);
lean_dec(x_168);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; lean_object* x_172; 
lean_dec(x_166);
x_171 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_172 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_164, x_165, x_171, x_1, x_2, x_3, x_4, x_5, x_6, x_169);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_Expr_fvar___override(x_18);
x_175 = l_Lean_Meta_Closure_pushFVarArg(x_174, x_1, x_2, x_3, x_4, x_5, x_6, x_173);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_7 = x_176;
goto _start;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_180 = x_172;
} else {
 lean_dec_ref(x_172);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; 
lean_dec(x_170);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_182 = l_Lean_Meta_Closure_collectExpr(x_165, x_1, x_2, x_3, x_4, x_5, x_6, x_169);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_185 = l_Lean_Meta_Closure_collectExpr(x_166, x_1, x_2, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; size_t x_233; size_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_st_ref_get(x_6, x_187);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_st_ref_take(x_2, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 4);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 5);
lean_inc(x_198);
x_199 = lean_ctor_get(x_191, 6);
lean_inc(x_199);
x_200 = lean_ctor_get(x_191, 7);
lean_inc(x_200);
x_201 = lean_ctor_get(x_191, 8);
lean_inc(x_201);
x_202 = lean_ctor_get(x_191, 9);
lean_inc(x_202);
x_203 = lean_ctor_get(x_191, 10);
lean_inc(x_203);
x_204 = lean_ctor_get(x_191, 11);
lean_inc(x_204);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 lean_ctor_release(x_191, 3);
 lean_ctor_release(x_191, 4);
 lean_ctor_release(x_191, 5);
 lean_ctor_release(x_191, 6);
 lean_ctor_release(x_191, 7);
 lean_ctor_release(x_191, 8);
 lean_ctor_release(x_191, 9);
 lean_ctor_release(x_191, 10);
 lean_ctor_release(x_191, 11);
 x_205 = x_191;
} else {
 lean_dec_ref(x_191);
 x_205 = lean_box(0);
}
x_206 = lean_unsigned_to_nat(0u);
x_207 = 0;
x_208 = 0;
lean_inc(x_186);
lean_inc(x_19);
x_209 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_19);
lean_ctor_set(x_209, 2, x_164);
lean_ctor_set(x_209, 3, x_183);
lean_ctor_set(x_209, 4, x_186);
lean_ctor_set_uint8(x_209, sizeof(void*)*5, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*5 + 1, x_208);
x_210 = lean_array_push(x_200, x_209);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 12, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_193);
lean_ctor_set(x_211, 1, x_194);
lean_ctor_set(x_211, 2, x_195);
lean_ctor_set(x_211, 3, x_196);
lean_ctor_set(x_211, 4, x_197);
lean_ctor_set(x_211, 5, x_198);
lean_ctor_set(x_211, 6, x_199);
lean_ctor_set(x_211, 7, x_210);
lean_ctor_set(x_211, 8, x_201);
lean_ctor_set(x_211, 9, x_202);
lean_ctor_set(x_211, 10, x_203);
lean_ctor_set(x_211, 11, x_204);
x_212 = lean_st_ref_set(x_2, x_211, x_192);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_st_ref_get(x_6, x_213);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_st_ref_take(x_2, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_217, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 3);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 4);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 5);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 6);
lean_inc(x_225);
x_226 = lean_ctor_get(x_217, 7);
lean_inc(x_226);
x_227 = lean_ctor_get(x_217, 8);
lean_inc(x_227);
x_228 = lean_ctor_get(x_217, 9);
lean_inc(x_228);
x_229 = lean_ctor_get(x_217, 10);
lean_inc(x_229);
x_230 = lean_ctor_get(x_217, 11);
lean_inc(x_230);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 lean_ctor_release(x_217, 6);
 lean_ctor_release(x_217, 7);
 lean_ctor_release(x_217, 8);
 lean_ctor_release(x_217, 9);
 lean_ctor_release(x_217, 10);
 lean_ctor_release(x_217, 11);
 x_231 = x_217;
} else {
 lean_dec_ref(x_217);
 x_231 = lean_box(0);
}
x_232 = lean_array_get_size(x_224);
x_233 = lean_usize_of_nat(x_232);
lean_dec(x_232);
x_234 = 0;
x_235 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_186, x_233, x_234, x_224);
lean_dec(x_186);
if (lean_is_scalar(x_231)) {
 x_236 = lean_alloc_ctor(0, 12, 0);
} else {
 x_236 = x_231;
}
lean_ctor_set(x_236, 0, x_219);
lean_ctor_set(x_236, 1, x_220);
lean_ctor_set(x_236, 2, x_221);
lean_ctor_set(x_236, 3, x_222);
lean_ctor_set(x_236, 4, x_223);
lean_ctor_set(x_236, 5, x_235);
lean_ctor_set(x_236, 6, x_225);
lean_ctor_set(x_236, 7, x_226);
lean_ctor_set(x_236, 8, x_227);
lean_ctor_set(x_236, 9, x_228);
lean_ctor_set(x_236, 10, x_229);
lean_ctor_set(x_236, 11, x_230);
x_237 = lean_st_ref_set(x_2, x_236, x_218);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_7 = x_238;
goto _start;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_183);
lean_dec(x_164);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = lean_ctor_get(x_185, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_185, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_242 = x_185;
} else {
 lean_dec_ref(x_185);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_244 = lean_ctor_get(x_182, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_182, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_246 = x_182;
} else {
 lean_dec_ref(x_182);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_20);
if (x_248 == 0)
{
return x_20;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_20, 0);
x_250 = lean_ctor_get(x_20, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_20);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
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
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
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
x_54 = lean_ctor_get_uint8(x_11, 13);
lean_dec(x_11);
x_55 = 1;
x_56 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_56, 0, x_42);
lean_ctor_set_uint8(x_56, 1, x_43);
lean_ctor_set_uint8(x_56, 2, x_44);
lean_ctor_set_uint8(x_56, 3, x_45);
lean_ctor_set_uint8(x_56, 4, x_46);
lean_ctor_set_uint8(x_56, 5, x_47);
lean_ctor_set_uint8(x_56, 6, x_48);
lean_ctor_set_uint8(x_56, 7, x_55);
lean_ctor_set_uint8(x_56, 8, x_49);
lean_ctor_set_uint8(x_56, 9, x_50);
lean_ctor_set_uint8(x_56, 10, x_51);
lean_ctor_set_uint8(x_56, 11, x_52);
lean_ctor_set_uint8(x_56, 12, x_53);
lean_ctor_set_uint8(x_56, 13, x_54);
lean_ctor_set(x_5, 0, x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_60 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_61);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_58);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_74 = x_60;
} else {
 lean_dec_ref(x_60);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_78 = x_57;
} else {
 lean_dec_ref(x_57);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_80 = lean_ctor_get(x_5, 1);
x_81 = lean_ctor_get(x_5, 2);
x_82 = lean_ctor_get(x_5, 3);
x_83 = lean_ctor_get(x_5, 4);
x_84 = lean_ctor_get(x_5, 5);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_5);
x_85 = lean_ctor_get_uint8(x_11, 0);
x_86 = lean_ctor_get_uint8(x_11, 1);
x_87 = lean_ctor_get_uint8(x_11, 2);
x_88 = lean_ctor_get_uint8(x_11, 3);
x_89 = lean_ctor_get_uint8(x_11, 4);
x_90 = lean_ctor_get_uint8(x_11, 5);
x_91 = lean_ctor_get_uint8(x_11, 6);
x_92 = lean_ctor_get_uint8(x_11, 8);
x_93 = lean_ctor_get_uint8(x_11, 9);
x_94 = lean_ctor_get_uint8(x_11, 10);
x_95 = lean_ctor_get_uint8(x_11, 11);
x_96 = lean_ctor_get_uint8(x_11, 12);
x_97 = lean_ctor_get_uint8(x_11, 13);
if (lean_is_exclusive(x_11)) {
 x_98 = x_11;
} else {
 lean_dec_ref(x_11);
 x_98 = lean_box(0);
}
x_99 = 1;
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 0, 14);
} else {
 x_100 = x_98;
}
lean_ctor_set_uint8(x_100, 0, x_85);
lean_ctor_set_uint8(x_100, 1, x_86);
lean_ctor_set_uint8(x_100, 2, x_87);
lean_ctor_set_uint8(x_100, 3, x_88);
lean_ctor_set_uint8(x_100, 4, x_89);
lean_ctor_set_uint8(x_100, 5, x_90);
lean_ctor_set_uint8(x_100, 6, x_91);
lean_ctor_set_uint8(x_100, 7, x_99);
lean_ctor_set_uint8(x_100, 8, x_92);
lean_ctor_set_uint8(x_100, 9, x_93);
lean_ctor_set_uint8(x_100, 10, x_94);
lean_ctor_set_uint8(x_100, 11, x_95);
lean_ctor_set_uint8(x_100, 12, x_96);
lean_ctor_set_uint8(x_100, 13, x_97);
x_101 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_80);
lean_ctor_set(x_101, 2, x_81);
lean_ctor_set(x_101, 3, x_82);
lean_ctor_set(x_101, 4, x_83);
lean_ctor_set(x_101, 5, x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_101);
x_102 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_101, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_101);
x_105 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_101, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_Closure_process(x_3, x_4, x_101, x_6, x_7, x_8, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_106);
lean_dec(x_103);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
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
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
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
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
x_15 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_22, 5);
lean_inc(x_25);
x_26 = l_Array_reverse___rarg(x_25);
x_27 = lean_ctor_get(x_22, 6);
lean_inc(x_27);
x_28 = l_Array_append___rarg(x_26, x_27);
x_29 = lean_ctor_get(x_22, 7);
lean_inc(x_29);
x_30 = l_Array_reverse___rarg(x_29);
lean_inc(x_30);
x_31 = l_Lean_Meta_Closure_mkForall(x_30, x_23);
lean_inc(x_28);
x_32 = l_Lean_Meta_Closure_mkForall(x_28, x_31);
x_33 = l_Lean_Meta_Closure_mkLambda(x_30, x_24);
x_34 = l_Lean_Meta_Closure_mkLambda(x_28, x_33);
x_35 = lean_ctor_get(x_22, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 10);
lean_inc(x_37);
x_38 = l_Array_reverse___rarg(x_37);
x_39 = lean_ctor_get(x_22, 9);
lean_inc(x_39);
lean_dec(x_22);
x_40 = l_Array_append___rarg(x_38, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_ctor_get(x_42, 5);
lean_inc(x_46);
x_47 = l_Array_reverse___rarg(x_46);
x_48 = lean_ctor_get(x_42, 6);
lean_inc(x_48);
x_49 = l_Array_append___rarg(x_47, x_48);
x_50 = lean_ctor_get(x_42, 7);
lean_inc(x_50);
x_51 = l_Array_reverse___rarg(x_50);
lean_inc(x_51);
x_52 = l_Lean_Meta_Closure_mkForall(x_51, x_44);
lean_inc(x_49);
x_53 = l_Lean_Meta_Closure_mkForall(x_49, x_52);
x_54 = l_Lean_Meta_Closure_mkLambda(x_51, x_45);
x_55 = l_Lean_Meta_Closure_mkLambda(x_49, x_54);
x_56 = lean_ctor_get(x_42, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 10);
lean_inc(x_58);
x_59 = l_Array_reverse___rarg(x_58);
x_60 = lean_ctor_get(x_42, 9);
lean_inc(x_60);
lean_dec(x_42);
x_61 = l_Array_append___rarg(x_59, x_60);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_43);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_13);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
