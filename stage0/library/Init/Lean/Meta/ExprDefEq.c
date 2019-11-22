// Lean compiler output
// Module: Init.Lean.Meta.ExprDefEq
// Imports: Init.Lean.ProjFns Init.Lean.Meta.WHNF Init.Lean.Meta.InferType Init.Lean.Meta.FunInfo Init.Lean.Meta.LevelDefEq Init.Lean.Meta.Check Init.Lean.Meta.Offset
#include "runtime/lean.h"
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
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__visit(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9;
lean_object* l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toMessageData___closed__51;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setIsExprDefEqAuxRef(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkFVar___at_Lean_Meta_CheckAssignment_check___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache;
uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3;
extern lean_object* l_Lean_Meta_isExprDefEq___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_getStuckMVar___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__2;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__5;
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isReducible(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__findCached___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAuxImpl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at_Lean_Meta_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toMessageData___closed__4;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__3(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7;
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__findCached(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Literal_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAuxImpl___closed__1;
lean_object* l_Lean_Meta_isLevelDefEqAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_25__unfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAuxImpl___closed__2;
lean_object* l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_40__isDefEqWHNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkMVar___at_Lean_Meta_CheckAssignment_check___main___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2(lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isWellFormed___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19;
lean_object* l___private_Init_Lean_Meta_LevelDefEq_12__restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3;
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_37__isLetFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16;
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_25__unfold(lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10;
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1;
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_ParamInfo_inhabited;
lean_object* l_HashMapImp_insert___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUsingDefault(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_39__isDefEqProofIrrel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern uint8_t l_Bool_Inhabited;
lean_object* l_Lean_Meta_getConstAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignmentQuick_check(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEqAuxRef;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1;
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___main(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__simpAssignmentArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_36__etaEq___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_26__unfoldBothDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_40__isDefEqWHNF___at_Lean_Meta_isExprDefEqAuxImpl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
uint8_t l___private_Init_Lean_Meta_ExprDefEq_36__etaEq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__cache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object*);
lean_object* l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setIsExprDefEqAuxRef___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_9__etaExpandedAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8;
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_32__isDefEqDelta(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2;
lean_object* l_Lean_Meta_tryL(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5;
lean_object* l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14;
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_HasBeq;
lean_object* l_Lean_mkBVar(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18;
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object*);
uint8_t l_Lean_ReducibilityHints_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2;
lean_object* _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = (uint8_t)((x_5 << 24) >> 61);
x_9 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1;
x_10 = l_Lean_mkApp(x_4, x_9);
x_11 = l_Lean_mkLambda(x_2, x_8, x_3, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 5);
x_16 = l_PersistentArray_empty___closed__3;
lean_inc(x_14);
lean_inc(x_13);
lean_ctor_set(x_7, 5, x_16);
lean_inc(x_6);
x_25 = l_Lean_Meta_isExprDefEqAux(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_13, x_14, x_15, x_6, x_28);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_13, x_14, x_15, x_6, x_38);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_17 = x_48;
x_18 = x_49;
goto block_24;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_dec(x_25);
x_17 = x_50;
x_18 = x_51;
goto block_24;
}
block_24:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_13, x_14, x_15, x_6, x_18);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_67; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
x_54 = lean_ctor_get(x_7, 2);
x_55 = lean_ctor_get(x_7, 3);
x_56 = lean_ctor_get(x_7, 4);
x_57 = lean_ctor_get(x_7, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_58 = l_PersistentArray_empty___closed__3;
lean_inc(x_53);
lean_inc(x_52);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_58);
lean_inc(x_6);
x_67 = l_Lean_Meta_isExprDefEqAux(x_1, x_11, x_6, x_59);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_52, x_53, x_57, x_6, x_70);
lean_dec(x_6);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_68);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_dec(x_67);
x_76 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_52, x_53, x_57, x_6, x_79);
lean_dec(x_6);
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
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_6);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_dec(x_76);
x_60 = x_87;
x_61 = x_88;
goto block_66;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_67, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
lean_dec(x_67);
x_60 = x_89;
x_61 = x_90;
goto block_66;
}
block_66:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_52, x_53, x_57, x_6, x_61);
lean_dec(x_6);
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
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isLambda(x_1);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isLambda(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_Meta_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l_Lean_Meta_whnfUsingDefault(x_11, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_14, sizeof(void*)*3);
lean_dec(x_14);
x_20 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1(x_1, x_16, x_17, x_18, x_19, x_3, x_15);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Lean_Expr_9__etaExpandedAux___main(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_metavar_ctx_is_expr_assigned(x_17, x_10);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_12);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_metavar_ctx_is_expr_assigned(x_22, x_10);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_11, 0, x_31);
return x_11;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
}
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isEtaUnassignedMVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_40; 
x_12 = lean_array_fget(x_1, x_4);
x_13 = l_Lean_Expr_Inhabited;
x_14 = lean_array_get(x_13, x_2, x_4);
x_15 = lean_array_get(x_13, x_3, x_4);
x_40 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_6);
x_42 = l_Lean_Meta_isExprDefEqAux(x_14, x_15, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_42, 0, x_47);
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_4, x_52);
lean_dec(x_4);
x_4 = x_53;
x_7 = x_51;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_inc(x_14);
x_59 = l_Lean_Meta_isEtaUnassignedMVar(x_14, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_15);
x_63 = l_Lean_Meta_isEtaUnassignedMVar(x_15, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unbox(x_64);
lean_dec(x_64);
x_16 = x_66;
x_17 = x_65;
goto block_39;
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
lean_dec(x_59);
x_72 = lean_unbox(x_60);
lean_dec(x_60);
x_16 = x_72;
x_17 = x_71;
goto block_39;
}
}
else
{
uint8_t x_73; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_59);
if (x_73 == 0)
{
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_59, 0);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_59);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_12);
lean_inc(x_14);
x_77 = l_Lean_Meta_isEtaUnassignedMVar(x_14, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
lean_inc(x_15);
x_81 = l_Lean_Meta_isEtaUnassignedMVar(x_15, x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_16 = x_84;
x_17 = x_83;
goto block_39;
}
else
{
uint8_t x_85; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
lean_dec(x_77);
x_90 = lean_unbox(x_78);
lean_dec(x_78);
x_16 = x_90;
x_17 = x_89;
goto block_39;
}
}
else
{
uint8_t x_91; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_77);
if (x_91 == 0)
{
return x_77;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_77, 0);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_77);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
block_39:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
x_20 = lean_array_push(x_5, x_4);
x_4 = x_19;
x_5 = x_20;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_22; 
lean_inc(x_6);
x_22 = l_Lean_Meta_isExprDefEqAux(x_14, x_15, x_6, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_4, x_32);
lean_dec(x_4);
x_4 = x_33;
x_7 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_1, x_4);
x_13 = lean_array_fget(x_2, x_4);
lean_inc(x_5);
x_14 = l_Lean_Meta_isExprDefEqAux(x_12, x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_23;
x_6 = x_21;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_1, x_2, lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; uint8_t x_19; 
x_19 = lean_nat_dec_lt(x_8, x_7);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_95; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_23 = lean_array_fget(x_6, x_8);
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_1, x_23);
x_26 = lean_array_get(x_24, x_2, x_23);
x_109 = l_Lean_Meta_ParamInfo_inhabited;
x_110 = lean_array_get(x_109, x_3, x_23);
lean_dec(x_23);
x_111 = lean_ctor_get_uint8(x_110, sizeof(void*)*1 + 1);
lean_dec(x_110);
if (x_111 == 0)
{
if (x_5 == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_95 = x_112;
goto block_108;
}
else
{
x_27 = x_10;
goto block_94;
}
}
else
{
if (x_5 == 0)
{
x_27 = x_10;
goto block_94;
}
else
{
lean_object* x_113; 
x_113 = lean_box(0);
x_95 = x_113;
goto block_108;
}
}
block_94:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 2);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; 
x_32 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 5);
x_33 = 1;
x_34 = l_Lean_Meta_TransparencyMode_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
x_36 = l_Lean_Meta_isExprDefEqAux(x_25, x_26, x_35, x_27);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = 1;
x_11 = x_40;
x_12 = x_39;
goto block_18;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = 0;
x_11 = x_42;
x_12 = x_41;
goto block_18;
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 5, x_33);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_30);
x_48 = l_Lean_Meta_isExprDefEqAux(x_25, x_26, x_47, x_27);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = 1;
x_11 = x_52;
x_12 = x_51;
goto block_18;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = 0;
x_11 = x_54;
x_12 = x_53;
goto block_18;
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
x_61 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 2);
x_63 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 3);
x_64 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 4);
x_65 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 5);
lean_inc(x_59);
lean_dec(x_28);
x_66 = 1;
x_67 = l_Lean_Meta_TransparencyMode_lt(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_60);
lean_ctor_set_uint8(x_68, sizeof(void*)*1 + 1, x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*1 + 2, x_62);
lean_ctor_set_uint8(x_68, sizeof(void*)*1 + 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*1 + 4, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*1 + 5, x_65);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_29);
lean_ctor_set(x_69, 2, x_30);
x_70 = l_Lean_Meta_isExprDefEqAux(x_25, x_26, x_69, x_27);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = 1;
x_11 = x_74;
x_12 = x_73;
goto block_18;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = 0;
x_11 = x_76;
x_12 = x_75;
goto block_18;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
lean_dec(x_8);
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_79 = x_70;
} else {
 lean_dec_ref(x_70);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_81, 0, x_59);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_60);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 1, x_61);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 2, x_62);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 3, x_63);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 4, x_64);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 5, x_66);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_29);
lean_ctor_set(x_82, 2, x_30);
x_83 = l_Lean_Meta_isExprDefEqAux(x_25, x_26, x_82, x_27);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = 1;
x_11 = x_87;
x_12 = x_86;
goto block_18;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = 0;
x_11 = x_89;
x_12 = x_88;
goto block_18;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_8);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
block_108:
{
lean_object* x_96; 
lean_dec(x_95);
lean_inc(x_9);
lean_inc(x_25);
x_96 = l_Lean_Meta_synthPending(x_25, x_9, x_10);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_9);
lean_inc(x_26);
x_98 = l_Lean_Meta_synthPending(x_26, x_9, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_27 = x_99;
goto block_94;
}
else
{
uint8_t x_100; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
x_104 = !lean_is_exclusive(x_96);
if (x_104 == 0)
{
return x_96;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_96, 0);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_96);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
block_18:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_8 = x_14;
x_10 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
x_16 = lean_box(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_4);
x_12 = l_Lean_Meta_getFunInfoNArgs(x_1, x_6, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_empty___closed__1;
lean_inc(x_4);
x_18 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_15, x_2, x_3, x_16, x_17, x_4, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_array_get_size(x_15);
lean_inc(x_4);
x_31 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_2, x_3, lean_box(0), x_30, x_4, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_array_get_size(x_29);
x_40 = lean_unbox(x_32);
lean_dec(x_32);
x_41 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1(x_2, x_3, x_15, x_29, x_40, x_29, x_39, x_16, x_4, x_38);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
lean_dec(x_53);
x_54 = 0;
x_55 = lean_box(x_54);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_41);
if (x_60 == 0)
{
return x_41;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_41, 0);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_41);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_31);
if (x_64 == 0)
{
return x_31;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_31, 0);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_31);
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
lean_dec(x_15);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_12);
if (x_72 == 0)
{
return x_12;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_12);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___spec__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_1, x_3);
lean_inc(x_5);
x_11 = l_Lean_Meta_getFVarLocalDecl(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_array_get(x_15, x_2, x_3);
lean_inc(x_5);
lean_inc(x_14);
x_17 = l_Lean_Meta_isExprDefEqAux(x_14, x_16, x_5, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_5);
x_25 = l_Lean_Meta_isClass(x_14, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_3 = x_29;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_3, x_33);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_5, 2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_10);
x_38 = lean_array_push(x_36, x_37);
lean_ctor_set(x_5, 2, x_38);
x_3 = x_34;
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get(x_5, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_10);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
x_3 = x_34;
x_5 = x_45;
x_6 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isDefEqBindingDomain(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_expr_instantiate_rev(x_2, x_1);
x_10 = lean_expr_instantiate_rev(x_3, x_1);
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = l_Lean_Meta_isExprDefEqAux(x_9, x_10, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_array_fget(x_4, x_6);
lean_inc(x_7);
x_15 = l_Lean_Meta_getFVarLocalDecl(x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_5, x_6);
lean_inc(x_7);
lean_inc(x_18);
x_21 = l_Lean_Meta_isExprDefEqAux(x_18, x_20, x_7, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_7);
x_29 = l_Lean_Meta_isClass(x_18, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_6, x_32);
lean_dec(x_6);
x_6 = x_33;
x_8 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_6, x_37);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_14);
x_42 = lean_array_push(x_40, x_41);
lean_ctor_set(x_7, 2, x_42);
x_6 = x_38;
x_8 = x_35;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_14);
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_48);
x_6 = x_38;
x_7 = x_49;
x_8 = x_35;
goto _start;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_29);
if (x_51 == 0)
{
return x_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_29, 0);
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_3)) {
case 6:
{
if (lean_obj_tag(x_4) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_expr_instantiate_rev(x_20, x_2);
lean_dec(x_20);
x_25 = lean_expr_instantiate_rev(x_22, x_2);
x_26 = l_Lean_Meta_mkFreshId___rarg(x_7);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 0;
lean_inc(x_27);
x_30 = lean_local_ctx_mk_local_decl(x_1, x_27, x_19, x_24, x_29);
x_31 = l_Lean_mkFVar(x_27);
x_32 = lean_array_push(x_2, x_31);
x_33 = lean_array_push(x_5, x_25);
x_1 = x_30;
x_2 = x_32;
x_3 = x_21;
x_4 = x_23;
x_5 = x_33;
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_8 = x_35;
goto block_18;
}
}
case 7:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
x_41 = lean_expr_instantiate_rev(x_37, x_2);
lean_dec(x_37);
x_42 = lean_expr_instantiate_rev(x_39, x_2);
x_43 = l_Lean_Meta_mkFreshId___rarg(x_7);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = 0;
lean_inc(x_44);
x_47 = lean_local_ctx_mk_local_decl(x_1, x_44, x_36, x_41, x_46);
x_48 = l_Lean_mkFVar(x_44);
x_49 = lean_array_push(x_2, x_48);
x_50 = lean_array_push(x_5, x_42);
x_1 = x_47;
x_2 = x_49;
x_3 = x_38;
x_4 = x_40;
x_5 = x_50;
x_7 = x_45;
goto _start;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_8 = x_52;
goto block_18;
}
}
default: 
{
lean_object* x_53; 
x_53 = lean_box(0);
x_8 = x_53;
goto block_18;
}
}
block_18:
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1(x_2, x_3, x_4, x_2, x_5, x_11, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1(x_2, x_3, x_4, x_2, x_5, x_16, x_15, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isDefEqBindingDomain___main___at___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Array_empty___closed__1;
x_7 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_5, x_6, x_1, x_2, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_equal(x_4, x_1);
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
lean_object* l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__findCached(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1(x_4, x_1);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at___private_Init_Lean_Meta_ExprDefEq_7__findCached___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__findCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_equal(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
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
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_expr_equal(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(x_1, x_2, x_7);
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
x_13 = lean_expr_equal(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__3(x_13, x_15);
return x_17;
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__cache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_HashMapImp_insert___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__1(x_6, x_1, x_2);
lean_ctor_set(x_4, 2, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_13 = l_HashMapImp_insert___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__1(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at___private_Init_Lean_Meta_ExprDefEq_8__cache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_7__findCached___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_8__cache___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
x_2 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_28; 
x_28 = l_Lean_Expr_hasExprMVar(x_2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasFVar(x_2);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_box(0);
x_5 = x_31;
goto block_27;
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_5 = x_32;
goto block_27;
}
block_27:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_2, x_10, x_3, x_11);
lean_dec(x_3);
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
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_LocalContext_containsFVar(x_6, x_2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_LocalContext_findFVar(x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Expr_HasBeq;
lean_inc(x_2);
x_12 = l_Array_contains___rarg(x_11, x_10, x_2);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lean_Expr_HasBeq;
lean_inc(x_2);
x_20 = l_Array_contains___rarg(x_19, x_18, x_2);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_49; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_17, 4);
lean_inc(x_25);
lean_dec(x_17);
x_49 = l_Lean_Expr_hasExprMVar(x_25);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasFVar(x_25);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_25);
lean_ctor_set(x_51, 1, x_4);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_26 = x_52;
goto block_48;
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_26 = x_53;
goto block_48;
}
block_48:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_25, x_3, x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_3);
lean_inc(x_25);
x_30 = lean_apply_3(x_1, x_25, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_25, x_31, x_3, x_32);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_27, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_44);
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_4);
return x_54;
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_CheckAssignment_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_CheckAssignment_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_name_mk_numeral(x_9, x_10);
x_12 = lean_box(0);
x_13 = 0;
lean_inc(x_11);
x_14 = lean_metavar_ctx_mk_decl(x_8, x_11, x_12, x_1, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_4, 0, x_14);
x_17 = l_Lean_mkMVar(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_name_mk_numeral(x_20, x_21);
x_23 = lean_box(0);
x_24 = 0;
lean_inc(x_22);
x_25 = lean_metavar_ctx_mk_decl(x_19, x_22, x_23, x_1, x_2, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_21, x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_25);
x_29 = l_Lean_mkMVar(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 2);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
lean_inc(x_35);
lean_inc(x_34);
x_37 = lean_name_mk_numeral(x_34, x_35);
x_38 = lean_box(0);
x_39 = 0;
lean_inc(x_37);
x_40 = lean_metavar_ctx_mk_decl(x_32, x_37, x_38, x_1, x_2, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_35, x_41);
lean_dec(x_35);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_33);
x_45 = l_Lean_mkMVar(x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_mvarId_x21(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_6);
x_7 = lean_metavar_ctx_get_expr_assignment(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_name_eq(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_6);
x_10 = lean_metavar_ctx_find_decl(x_6, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
lean_inc(x_15);
x_18 = l_Lean_LocalContext_isSubPrefixOf(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_14, sizeof(void*)*4);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
uint8_t x_27; 
lean_inc(x_17);
x_27 = l_Lean_LocalContext_isSubPrefixOf(x_17, x_15);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_14, 2);
lean_inc(x_29);
lean_dec(x_14);
lean_inc(x_29);
lean_inc(x_17);
x_30 = l_Lean_MetavarContext_isWellFormed___main(x_6, x_17, x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_3);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_5);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_17, x_29, x_3, x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_40 = lean_metavar_ctx_assign_expr(x_39, x_5, x_38);
lean_ctor_set(x_36, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_ctor_get(x_36, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
lean_inc(x_41);
x_45 = lean_metavar_ctx_assign_expr(x_42, x_5, x_41);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_34, 1, x_46);
return x_34;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_34, 1);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
lean_inc(x_48);
x_53 = lean_metavar_ctx_assign_expr(x_49, x_5, x_48);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_ctor_get(x_7, 0);
lean_inc(x_63);
lean_dec(x_7);
x_87 = l_Lean_Expr_hasExprMVar(x_63);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_hasFVar(x_63);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_64 = x_90;
goto block_86;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_64 = x_91;
goto block_86;
}
block_86:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_64);
x_65 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_63, x_3, x_4);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_3);
lean_inc(x_63);
x_68 = lean_apply_3(x_1, x_63, x_3, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_63, x_69, x_3, x_70);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_63);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 0);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_68);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_65, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_66, 0);
lean_inc(x_82);
lean_dec(x_66);
lean_ctor_set(x_65, 0, x_82);
return x_65;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
lean_dec(x_66);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_expr_eqv(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkFVar___at_Lean_Meta_CheckAssignment_check___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_LocalContext_containsFVar(x_5, x_1);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_LocalContext_findFVar(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_46; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
lean_dec(x_15);
x_46 = l_Lean_Expr_hasExprMVar(x_22);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasFVar(x_22);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_23 = x_49;
goto block_45;
}
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_23 = x_50;
goto block_45;
}
block_45:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_23);
x_24 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_22, x_2, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
lean_inc(x_22);
x_27 = l_Lean_Meta_CheckAssignment_check___main(x_22, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_22, x_28, x_2, x_29);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_22);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkMVar___at_Lean_Meta_CheckAssignment_check___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Expr_mvarId_x21(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_metavar_ctx_get_expr_assignment(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_5);
x_9 = lean_metavar_ctx_find_decl(x_5, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_14);
x_17 = l_Lean_LocalContext_isSubPrefixOf(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
uint8_t x_26; 
lean_inc(x_16);
x_26 = l_Lean_LocalContext_isSubPrefixOf(x_16, x_14);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_13, 2);
lean_inc(x_28);
lean_dec(x_13);
lean_inc(x_28);
lean_inc(x_16);
x_29 = l_Lean_MetavarContext_isWellFormed___main(x_5, x_16, x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_2);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_16, x_28, x_2, x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_39 = lean_metavar_ctx_assign_expr(x_38, x_4, x_37);
lean_ctor_set(x_35, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
x_43 = lean_ctor_get(x_35, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_40);
x_44 = lean_metavar_ctx_assign_expr(x_41, x_4, x_40);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_33, 1, x_45);
return x_33;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
lean_inc(x_47);
x_52 = lean_metavar_ctx_assign_expr(x_48, x_4, x_47);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_4);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_86; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
lean_dec(x_6);
x_86 = l_Lean_Expr_hasExprMVar(x_62);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_hasFVar(x_62);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_3);
return x_88;
}
else
{
lean_object* x_89; 
x_89 = lean_box(0);
x_63 = x_89;
goto block_85;
}
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_63 = x_90;
goto block_85;
}
block_85:
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_63);
x_64 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_62, x_2, x_3);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_2);
lean_inc(x_62);
x_67 = l_Lean_Meta_CheckAssignment_check___main(x_62, x_2, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_68);
x_70 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_62, x_68, x_2, x_69);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_62);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_62);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_64, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
lean_dec(x_65);
lean_ctor_set(x_64, 0, x_81);
return x_64;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_check___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_22; uint8_t x_45; 
x_45 = l_Lean_Expr_hasExprMVar(x_1);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasFVar(x_1);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_22 = x_48;
goto block_44;
}
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_22 = x_49;
goto block_44;
}
block_44:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_22);
x_23 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_1, x_2, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Meta_CheckAssignment_checkFVar___at_Lean_Meta_CheckAssignment_check___main___spec__1(x_1, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_1, x_27, x_2, x_28);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
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
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_23, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
case 2:
{
lean_object* x_50; uint8_t x_73; 
x_73 = l_Lean_Expr_hasExprMVar(x_1);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_hasFVar(x_1);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_2);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_box(0);
x_50 = x_76;
goto block_72;
}
}
else
{
lean_object* x_77; 
x_77 = lean_box(0);
x_50 = x_77;
goto block_72;
}
block_72:
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_50);
x_51 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_1, x_2, x_3);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Meta_CheckAssignment_checkMVar___at_Lean_Meta_CheckAssignment_check___main___spec__4(x_1, x_2, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_1, x_55, x_2, x_56);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
lean_ctor_set(x_51, 0, x_68);
return x_51;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_dec(x_51);
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
lean_dec(x_52);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_112; uint8_t x_128; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_128 = l_Lean_Expr_hasExprMVar(x_78);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = l_Lean_Expr_hasFVar(x_78);
if (x_129 == 0)
{
x_80 = x_78;
x_81 = x_3;
goto block_111;
}
else
{
lean_object* x_130; 
x_130 = lean_box(0);
x_112 = x_130;
goto block_127;
}
}
else
{
lean_object* x_131; 
x_131 = lean_box(0);
x_112 = x_131;
goto block_127;
}
block_111:
{
lean_object* x_82; lean_object* x_83; lean_object* x_91; uint8_t x_107; 
x_107 = l_Lean_Expr_hasExprMVar(x_79);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Expr_hasFVar(x_79);
if (x_108 == 0)
{
lean_dec(x_2);
x_82 = x_79;
x_83 = x_81;
goto block_90;
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_91 = x_109;
goto block_106;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_91 = x_110;
goto block_106;
}
block_90:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_expr_update_app(x_1, x_80, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_1);
x_86 = l_Lean_Expr_Inhabited;
x_87 = l_Lean_Expr_updateApp_x21___closed__1;
x_88 = lean_panic_fn(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
block_106:
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_91);
x_92 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_79, x_2, x_81);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_2);
lean_inc(x_79);
x_95 = l_Lean_Meta_CheckAssignment_check___main(x_79, x_2, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_96);
x_98 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_79, x_96, x_2, x_97);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_82 = x_96;
x_83 = x_99;
goto block_90;
}
else
{
uint8_t x_100; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_79);
lean_dec(x_2);
x_104 = lean_ctor_get(x_92, 1);
lean_inc(x_104);
lean_dec(x_92);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
lean_dec(x_93);
x_82 = x_105;
x_83 = x_104;
goto block_90;
}
}
}
block_127:
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_112);
x_113 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_78, x_2, x_3);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_2);
lean_inc(x_78);
x_116 = l_Lean_Meta_CheckAssignment_check___main(x_78, x_2, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_78, x_117, x_2, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_80 = x_117;
x_81 = x_120;
goto block_111;
}
else
{
uint8_t x_121; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
return x_116;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_116);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_78);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_dec(x_113);
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec(x_114);
x_80 = x_126;
x_81 = x_125;
goto block_111;
}
}
}
case 6:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_168; uint8_t x_184; 
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 2);
lean_inc(x_133);
x_184 = l_Lean_Expr_hasExprMVar(x_132);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Lean_Expr_hasFVar(x_132);
if (x_185 == 0)
{
x_134 = x_132;
x_135 = x_3;
goto block_167;
}
else
{
lean_object* x_186; 
x_186 = lean_box(0);
x_168 = x_186;
goto block_183;
}
}
else
{
lean_object* x_187; 
x_187 = lean_box(0);
x_168 = x_187;
goto block_183;
}
block_167:
{
lean_object* x_136; lean_object* x_137; lean_object* x_147; uint8_t x_163; 
x_163 = l_Lean_Expr_hasExprMVar(x_133);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Expr_hasFVar(x_133);
if (x_164 == 0)
{
lean_dec(x_2);
x_136 = x_133;
x_137 = x_135;
goto block_146;
}
else
{
lean_object* x_165; 
x_165 = lean_box(0);
x_147 = x_165;
goto block_162;
}
}
else
{
lean_object* x_166; 
x_166 = lean_box(0);
x_147 = x_166;
goto block_162;
}
block_146:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_139 = (uint8_t)((x_138 << 24) >> 61);
x_140 = lean_expr_update_lambda(x_1, x_139, x_134, x_136);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_137);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_1);
x_142 = l_Lean_Expr_Inhabited;
x_143 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_144 = lean_panic_fn(x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
return x_145;
}
}
block_162:
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_147);
x_148 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_133, x_2, x_135);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_2);
lean_inc(x_133);
x_151 = l_Lean_Meta_CheckAssignment_check___main(x_133, x_2, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_152);
x_154 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_133, x_152, x_2, x_153);
lean_dec(x_2);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_136 = x_152;
x_137 = x_155;
goto block_146;
}
else
{
uint8_t x_156; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_151);
if (x_156 == 0)
{
return x_151;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_151, 0);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_151);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_133);
lean_dec(x_2);
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
lean_dec(x_148);
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
lean_dec(x_149);
x_136 = x_161;
x_137 = x_160;
goto block_146;
}
}
}
block_183:
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_168);
x_169 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_132, x_2, x_3);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_2);
lean_inc(x_132);
x_172 = l_Lean_Meta_CheckAssignment_check___main(x_132, x_2, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_173);
x_175 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_132, x_173, x_2, x_174);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_134 = x_173;
x_135 = x_176;
goto block_167;
}
else
{
uint8_t x_177; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_172);
if (x_177 == 0)
{
return x_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_172);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_132);
x_181 = lean_ctor_get(x_169, 1);
lean_inc(x_181);
lean_dec(x_169);
x_182 = lean_ctor_get(x_170, 0);
lean_inc(x_182);
lean_dec(x_170);
x_134 = x_182;
x_135 = x_181;
goto block_167;
}
}
}
case 7:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_224; uint8_t x_240; 
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_1, 2);
lean_inc(x_189);
x_240 = l_Lean_Expr_hasExprMVar(x_188);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Expr_hasFVar(x_188);
if (x_241 == 0)
{
x_190 = x_188;
x_191 = x_3;
goto block_223;
}
else
{
lean_object* x_242; 
x_242 = lean_box(0);
x_224 = x_242;
goto block_239;
}
}
else
{
lean_object* x_243; 
x_243 = lean_box(0);
x_224 = x_243;
goto block_239;
}
block_223:
{
lean_object* x_192; lean_object* x_193; lean_object* x_203; uint8_t x_219; 
x_219 = l_Lean_Expr_hasExprMVar(x_189);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = l_Lean_Expr_hasFVar(x_189);
if (x_220 == 0)
{
lean_dec(x_2);
x_192 = x_189;
x_193 = x_191;
goto block_202;
}
else
{
lean_object* x_221; 
x_221 = lean_box(0);
x_203 = x_221;
goto block_218;
}
}
else
{
lean_object* x_222; 
x_222 = lean_box(0);
x_203 = x_222;
goto block_218;
}
block_202:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_195 = (uint8_t)((x_194 << 24) >> 61);
x_196 = lean_expr_update_forall(x_1, x_195, x_190, x_192);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_193);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_1);
x_198 = l_Lean_Expr_Inhabited;
x_199 = l_Lean_Expr_updateForallE_x21___closed__1;
x_200 = lean_panic_fn(x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_193);
return x_201;
}
}
block_218:
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_203);
x_204 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_189, x_2, x_191);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_2);
lean_inc(x_189);
x_207 = l_Lean_Meta_CheckAssignment_check___main(x_189, x_2, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_208);
x_210 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_189, x_208, x_2, x_209);
lean_dec(x_2);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_192 = x_208;
x_193 = x_211;
goto block_202;
}
else
{
uint8_t x_212; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_207);
if (x_212 == 0)
{
return x_207;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_207, 0);
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_207);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_189);
lean_dec(x_2);
x_216 = lean_ctor_get(x_204, 1);
lean_inc(x_216);
lean_dec(x_204);
x_217 = lean_ctor_get(x_205, 0);
lean_inc(x_217);
lean_dec(x_205);
x_192 = x_217;
x_193 = x_216;
goto block_202;
}
}
}
block_239:
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_224);
x_225 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_188, x_2, x_3);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
lean_inc(x_2);
lean_inc(x_188);
x_228 = l_Lean_Meta_CheckAssignment_check___main(x_188, x_2, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_229);
x_231 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_188, x_229, x_2, x_230);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_190 = x_229;
x_191 = x_232;
goto block_223;
}
else
{
uint8_t x_233; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_2);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_228);
if (x_233 == 0)
{
return x_228;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_228, 0);
x_235 = lean_ctor_get(x_228, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_228);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_188);
x_237 = lean_ctor_get(x_225, 1);
lean_inc(x_237);
lean_dec(x_225);
x_238 = lean_ctor_get(x_226, 0);
lean_inc(x_238);
lean_dec(x_226);
x_190 = x_238;
x_191 = x_237;
goto block_223;
}
}
}
case 8:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_302; uint8_t x_318; 
x_244 = lean_ctor_get(x_1, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_1, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_1, 3);
lean_inc(x_246);
x_318 = l_Lean_Expr_hasExprMVar(x_244);
if (x_318 == 0)
{
uint8_t x_319; 
x_319 = l_Lean_Expr_hasFVar(x_244);
if (x_319 == 0)
{
x_247 = x_244;
x_248 = x_3;
goto block_301;
}
else
{
lean_object* x_320; 
x_320 = lean_box(0);
x_302 = x_320;
goto block_317;
}
}
else
{
lean_object* x_321; 
x_321 = lean_box(0);
x_302 = x_321;
goto block_317;
}
block_301:
{
lean_object* x_249; lean_object* x_250; lean_object* x_281; uint8_t x_297; 
x_297 = l_Lean_Expr_hasExprMVar(x_245);
if (x_297 == 0)
{
uint8_t x_298; 
x_298 = l_Lean_Expr_hasFVar(x_245);
if (x_298 == 0)
{
x_249 = x_245;
x_250 = x_248;
goto block_280;
}
else
{
lean_object* x_299; 
x_299 = lean_box(0);
x_281 = x_299;
goto block_296;
}
}
else
{
lean_object* x_300; 
x_300 = lean_box(0);
x_281 = x_300;
goto block_296;
}
block_280:
{
lean_object* x_251; lean_object* x_252; lean_object* x_260; uint8_t x_276; 
x_276 = l_Lean_Expr_hasExprMVar(x_246);
if (x_276 == 0)
{
uint8_t x_277; 
x_277 = l_Lean_Expr_hasFVar(x_246);
if (x_277 == 0)
{
lean_dec(x_2);
x_251 = x_246;
x_252 = x_250;
goto block_259;
}
else
{
lean_object* x_278; 
x_278 = lean_box(0);
x_260 = x_278;
goto block_275;
}
}
else
{
lean_object* x_279; 
x_279 = lean_box(0);
x_260 = x_279;
goto block_275;
}
block_259:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_expr_update_let(x_1, x_247, x_249, x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_251);
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_1);
x_255 = l_Lean_Expr_Inhabited;
x_256 = l_Lean_Expr_updateLet_x21___closed__1;
x_257 = lean_panic_fn(x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_252);
return x_258;
}
}
block_275:
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_260);
x_261 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_246, x_2, x_250);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_inc(x_2);
lean_inc(x_246);
x_264 = l_Lean_Meta_CheckAssignment_check___main(x_246, x_2, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_265);
x_267 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_246, x_265, x_2, x_266);
lean_dec(x_2);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_251 = x_265;
x_252 = x_268;
goto block_259;
}
else
{
uint8_t x_269; 
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_2);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_264);
if (x_269 == 0)
{
return x_264;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_264, 0);
x_271 = lean_ctor_get(x_264, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_264);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_246);
lean_dec(x_2);
x_273 = lean_ctor_get(x_261, 1);
lean_inc(x_273);
lean_dec(x_261);
x_274 = lean_ctor_get(x_262, 0);
lean_inc(x_274);
lean_dec(x_262);
x_251 = x_274;
x_252 = x_273;
goto block_259;
}
}
}
block_296:
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_281);
x_282 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_245, x_2, x_248);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_2);
lean_inc(x_245);
x_285 = l_Lean_Meta_CheckAssignment_check___main(x_245, x_2, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_286);
x_288 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_245, x_286, x_2, x_287);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_249 = x_286;
x_250 = x_289;
goto block_280;
}
else
{
uint8_t x_290; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_2);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_285);
if (x_290 == 0)
{
return x_285;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_285, 0);
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_285);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_245);
x_294 = lean_ctor_get(x_282, 1);
lean_inc(x_294);
lean_dec(x_282);
x_295 = lean_ctor_get(x_283, 0);
lean_inc(x_295);
lean_dec(x_283);
x_249 = x_295;
x_250 = x_294;
goto block_280;
}
}
}
block_317:
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_302);
x_303 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_244, x_2, x_3);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
lean_inc(x_2);
lean_inc(x_244);
x_306 = l_Lean_Meta_CheckAssignment_check___main(x_244, x_2, x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
lean_inc(x_307);
x_309 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_244, x_307, x_2, x_308);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_247 = x_307;
x_248 = x_310;
goto block_301;
}
else
{
uint8_t x_311; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_2);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_306);
if (x_311 == 0)
{
return x_306;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_306, 0);
x_313 = lean_ctor_get(x_306, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_306);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_244);
x_315 = lean_ctor_get(x_303, 1);
lean_inc(x_315);
lean_dec(x_303);
x_316 = lean_ctor_get(x_304, 0);
lean_inc(x_316);
lean_dec(x_304);
x_247 = x_316;
x_248 = x_315;
goto block_301;
}
}
}
case 10:
{
lean_object* x_322; lean_object* x_323; uint8_t x_339; 
x_322 = lean_ctor_get(x_1, 1);
lean_inc(x_322);
x_339 = l_Lean_Expr_hasExprMVar(x_322);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = l_Lean_Expr_hasFVar(x_322);
if (x_340 == 0)
{
lean_dec(x_2);
x_4 = x_322;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_341; 
x_341 = lean_box(0);
x_323 = x_341;
goto block_338;
}
}
else
{
lean_object* x_342; 
x_342 = lean_box(0);
x_323 = x_342;
goto block_338;
}
block_338:
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_323);
x_324 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_322, x_2, x_3);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
lean_inc(x_2);
lean_inc(x_322);
x_327 = l_Lean_Meta_CheckAssignment_check___main(x_322, x_2, x_326);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
lean_inc(x_328);
x_330 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_322, x_328, x_2, x_329);
lean_dec(x_2);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_4 = x_328;
x_5 = x_331;
goto block_12;
}
else
{
uint8_t x_332; 
lean_dec(x_322);
lean_dec(x_2);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_327);
if (x_332 == 0)
{
return x_327;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_327, 0);
x_334 = lean_ctor_get(x_327, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_327);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_322);
lean_dec(x_2);
x_336 = lean_ctor_get(x_324, 1);
lean_inc(x_336);
lean_dec(x_324);
x_337 = lean_ctor_get(x_325, 0);
lean_inc(x_337);
lean_dec(x_325);
x_4 = x_337;
x_5 = x_336;
goto block_12;
}
}
}
case 11:
{
lean_object* x_343; lean_object* x_344; uint8_t x_360; 
x_343 = lean_ctor_get(x_1, 2);
lean_inc(x_343);
x_360 = l_Lean_Expr_hasExprMVar(x_343);
if (x_360 == 0)
{
uint8_t x_361; 
x_361 = l_Lean_Expr_hasFVar(x_343);
if (x_361 == 0)
{
lean_dec(x_2);
x_13 = x_343;
x_14 = x_3;
goto block_21;
}
else
{
lean_object* x_362; 
x_362 = lean_box(0);
x_344 = x_362;
goto block_359;
}
}
else
{
lean_object* x_363; 
x_363 = lean_box(0);
x_344 = x_363;
goto block_359;
}
block_359:
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_344);
x_345 = l___private_Init_Lean_Meta_ExprDefEq_7__findCached(x_343, x_2, x_3);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
lean_inc(x_2);
lean_inc(x_343);
x_348 = l_Lean_Meta_CheckAssignment_check___main(x_343, x_2, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
lean_inc(x_349);
x_351 = l___private_Init_Lean_Meta_ExprDefEq_8__cache(x_343, x_349, x_2, x_350);
lean_dec(x_2);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_13 = x_349;
x_14 = x_352;
goto block_21;
}
else
{
uint8_t x_353; 
lean_dec(x_343);
lean_dec(x_2);
lean_dec(x_1);
x_353 = !lean_is_exclusive(x_348);
if (x_353 == 0)
{
return x_348;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_348, 0);
x_355 = lean_ctor_get(x_348, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_348);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_343);
lean_dec(x_2);
x_357 = lean_ctor_get(x_345, 1);
lean_inc(x_357);
lean_dec(x_345);
x_358 = lean_ctor_get(x_346, 0);
lean_inc(x_358);
lean_dec(x_346);
x_13 = x_358;
x_14 = x_357;
goto block_21;
}
}
}
case 12:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_1);
x_364 = l_Lean_Meta_CheckAssignment_check___main___closed__1;
x_365 = l_unreachable_x21___rarg(x_364);
x_366 = lean_apply_2(x_365, x_2, x_3);
return x_366;
}
default: 
{
lean_object* x_367; 
lean_dec(x_2);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_1);
lean_ctor_set(x_367, 1, x_3);
return x_367;
}
}
block_12:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_expr_update_mdata(x_1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Lean_Expr_Inhabited;
x_9 = l_Lean_Expr_updateMData_x21___closed__2;
x_10 = lean_panic_fn(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
block_21:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_update_proj(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Expr_Inhabited;
x_18 = l_Lean_Expr_updateProj_x21___closed__2;
x_19 = lean_panic_fn(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_CheckAssignment_check___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_check___closed__2;
x_2 = l_Lean_Meta_isExprDefEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assignment");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("occursCheck");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatEntry___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("outOfScopeFVar");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" @ ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("readOnlyMVarWithBiggerLCtx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mvarTypeNotWellFormedInSmallerLCtx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6;
x_12 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_11, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_mkMVar(x_1);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_26 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_24, x_25);
x_27 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5;
x_33 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_32, x_31, x_5, x_21);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
case 2:
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_71; uint8_t x_72; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
lean_dec(x_4);
x_71 = lean_ctor_get(x_6, 4);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = 0;
x_43 = x_73;
x_44 = x_6;
goto block_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13;
x_75 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_74, x_5, x_6);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_43 = x_78;
x_44 = x_77;
goto block_70;
}
block_70:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_47 = l_Lean_mkFVar(x_42);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12;
x_50 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_mkMVar(x_1);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_56 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_54, x_55);
x_57 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_59 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_3);
x_61 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9;
x_63 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_62, x_61, x_5, x_44);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
case 3:
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_108; uint8_t x_109; 
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
lean_dec(x_4);
x_108 = lean_ctor_get(x_6, 4);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*1);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = 0;
x_80 = x_110;
x_81 = x_6;
goto block_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16;
x_112 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_111, x_5, x_6);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_80 = x_115;
x_81 = x_114;
goto block_107;
}
block_107:
{
if (x_80 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_84 = l_Lean_mkMVar(x_79);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12;
x_87 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_mkMVar(x_1);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_93 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_91, x_92);
x_94 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_96 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_3);
x_98 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15;
x_100 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_99, x_98, x_5, x_81);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
case 4:
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_145; uint8_t x_146; 
x_116 = lean_ctor_get(x_4, 0);
lean_inc(x_116);
lean_dec(x_4);
x_145 = lean_ctor_get(x_6, 4);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = 0;
x_117 = x_147;
x_118 = x_6;
goto block_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19;
x_149 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_148, x_5, x_6);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_117 = x_152;
x_118 = x_151;
goto block_144;
}
block_144:
{
if (x_117 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
lean_dec(x_3);
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_121 = l_Lean_mkMVar(x_116);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12;
x_124 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_mkMVar(x_1);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_130 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_128, x_129);
x_131 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_133 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_3);
x_135 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18;
x_137 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_136, x_135, x_5, x_118);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
x_140 = lean_box(0);
lean_ctor_set(x_137, 0, x_140);
return x_137;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
default: 
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_4, 0);
lean_inc(x_153);
lean_dec(x_4);
x_154 = lean_ctor_get(x_6, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_157, 2, x_156);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasExprMVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 1;
x_6 = lean_box(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_apply_1(x_1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_apply_1(x_1, x_2);
return x_8;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___main(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_8)) {
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_LocalContext_contains(x_10, x_9);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_9);
x_12 = lean_local_ctx_find(x_4, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1(x_7, x_9, x_7, x_13, x_14);
lean_dec(x_13);
lean_dec(x_9);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_box(x_16);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = lean_box(x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_20);
x_21 = lean_array_get_size(x_7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2(x_7, x_9, x_7, x_21, x_22);
lean_dec(x_21);
lean_dec(x_9);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = lean_box(x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
x_27 = lean_box(x_26);
return x_27;
}
}
else
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_9);
x_28 = 0;
x_29 = lean_box(x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_4);
x_30 = 1;
x_31 = lean_box(x_30);
return x_31;
}
}
case 2:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
lean_inc(x_32);
lean_inc(x_3);
x_33 = lean_metavar_ctx_get_expr_assignment(x_3, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = lean_name_eq(x_32, x_6);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_3);
x_35 = lean_metavar_ctx_find_decl(x_3, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_3);
x_36 = 0;
x_37 = lean_box(x_36);
return x_37;
}
else
{
if (x_1 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_40);
lean_inc(x_39);
x_41 = l_Lean_LocalContext_isSubPrefixOf(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_45 = 0;
x_46 = lean_box(x_45);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
lean_dec(x_38);
if (x_47 == 0)
{
if (x_2 == 0)
{
uint8_t x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_39);
x_48 = 1;
x_49 = lean_box(x_48);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l_Lean_LocalContext_isSubPrefixOf(x_40, x_39);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = 1;
x_52 = lean_box(x_51);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; 
x_53 = 0;
x_54 = lean_box(x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_39);
x_55 = 0;
x_56 = lean_box(x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
x_57 = 1;
x_58 = lean_box(x_57);
return x_58;
}
}
else
{
uint8_t x_59; lean_object* x_60; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_3);
x_59 = 0;
x_60 = lean_box(x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; lean_object* x_62; 
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_3);
x_61 = 0;
x_62 = lean_box(x_61);
return x_62;
}
}
else
{
uint8_t x_63; lean_object* x_64; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_3);
x_63 = 0;
x_64 = lean_box(x_63);
return x_64;
}
}
case 5:
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_dec(x_8);
x_67 = l_Lean_Expr_hasExprMVar(x_65);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasFVar(x_65);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_65);
x_69 = l_Lean_Expr_hasExprMVar(x_66);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasFVar(x_66);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = 1;
x_72 = lean_box(x_71);
return x_72;
}
else
{
x_8 = x_66;
goto _start;
}
}
else
{
x_8 = x_66;
goto _start;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_75 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = 0;
x_78 = lean_box(x_77);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasExprMVar(x_66);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasFVar(x_66);
if (x_80 == 0)
{
uint8_t x_81; lean_object* x_82; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = 1;
x_82 = lean_box(x_81);
return x_82;
}
else
{
x_8 = x_66;
goto _start;
}
}
else
{
x_8 = x_66;
goto _start;
}
}
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = 0;
x_88 = lean_box(x_87);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasExprMVar(x_66);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_hasFVar(x_66);
if (x_90 == 0)
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = 1;
x_92 = lean_box(x_91);
return x_92;
}
else
{
x_8 = x_66;
goto _start;
}
}
else
{
x_8 = x_66;
goto _start;
}
}
}
}
case 6:
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_8, 2);
lean_inc(x_96);
lean_dec(x_8);
x_97 = l_Lean_Expr_hasExprMVar(x_95);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Expr_hasFVar(x_95);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_95);
x_99 = l_Lean_Expr_hasExprMVar(x_96);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_hasFVar(x_96);
if (x_100 == 0)
{
uint8_t x_101; lean_object* x_102; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = 1;
x_102 = lean_box(x_101);
return x_102;
}
else
{
x_8 = x_96;
goto _start;
}
}
else
{
x_8 = x_96;
goto _start;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_95);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = 0;
x_108 = lean_box(x_107);
return x_108;
}
else
{
uint8_t x_109; 
x_109 = l_Lean_Expr_hasExprMVar(x_96);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Expr_hasFVar(x_96);
if (x_110 == 0)
{
uint8_t x_111; lean_object* x_112; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = 1;
x_112 = lean_box(x_111);
return x_112;
}
else
{
x_8 = x_96;
goto _start;
}
}
else
{
x_8 = x_96;
goto _start;
}
}
}
}
else
{
lean_object* x_115; uint8_t x_116; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_95);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
uint8_t x_117; lean_object* x_118; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = 0;
x_118 = lean_box(x_117);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasExprMVar(x_96);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = l_Lean_Expr_hasFVar(x_96);
if (x_120 == 0)
{
uint8_t x_121; lean_object* x_122; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = 1;
x_122 = lean_box(x_121);
return x_122;
}
else
{
x_8 = x_96;
goto _start;
}
}
else
{
x_8 = x_96;
goto _start;
}
}
}
}
case 7:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_8, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_8, 2);
lean_inc(x_126);
lean_dec(x_8);
x_127 = l_Lean_Expr_hasExprMVar(x_125);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasFVar(x_125);
if (x_128 == 0)
{
uint8_t x_129; 
lean_dec(x_125);
x_129 = l_Lean_Expr_hasExprMVar(x_126);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = l_Lean_Expr_hasFVar(x_126);
if (x_130 == 0)
{
uint8_t x_131; lean_object* x_132; 
lean_dec(x_126);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_131 = 1;
x_132 = lean_box(x_131);
return x_132;
}
else
{
x_8 = x_126;
goto _start;
}
}
else
{
x_8 = x_126;
goto _start;
}
}
else
{
lean_object* x_135; uint8_t x_136; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_135 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_125);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
uint8_t x_137; lean_object* x_138; 
lean_dec(x_126);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = 0;
x_138 = lean_box(x_137);
return x_138;
}
else
{
uint8_t x_139; 
x_139 = l_Lean_Expr_hasExprMVar(x_126);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Expr_hasFVar(x_126);
if (x_140 == 0)
{
uint8_t x_141; lean_object* x_142; 
lean_dec(x_126);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = 1;
x_142 = lean_box(x_141);
return x_142;
}
else
{
x_8 = x_126;
goto _start;
}
}
else
{
x_8 = x_126;
goto _start;
}
}
}
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_145 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_125);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
uint8_t x_147; lean_object* x_148; 
lean_dec(x_126);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = 0;
x_148 = lean_box(x_147);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasExprMVar(x_126);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasFVar(x_126);
if (x_150 == 0)
{
uint8_t x_151; lean_object* x_152; 
lean_dec(x_126);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = 1;
x_152 = lean_box(x_151);
return x_152;
}
else
{
x_8 = x_126;
goto _start;
}
}
else
{
x_8 = x_126;
goto _start;
}
}
}
}
case 8:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_188; 
x_155 = lean_ctor_get(x_8, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_8, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_8, 3);
lean_inc(x_157);
lean_dec(x_8);
x_188 = l_Lean_Expr_hasExprMVar(x_155);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = l_Lean_Expr_hasFVar(x_155);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_155);
x_190 = lean_box(0);
x_158 = x_190;
goto block_187;
}
else
{
lean_object* x_191; uint8_t x_192; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_155);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
uint8_t x_193; lean_object* x_194; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = 0;
x_194 = lean_box(x_193);
return x_194;
}
else
{
lean_object* x_195; 
x_195 = lean_box(0);
x_158 = x_195;
goto block_187;
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_196 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_155);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
uint8_t x_198; lean_object* x_199; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_198 = 0;
x_199 = lean_box(x_198);
return x_199;
}
else
{
lean_object* x_200; 
x_200 = lean_box(0);
x_158 = x_200;
goto block_187;
}
}
block_187:
{
uint8_t x_159; 
lean_dec(x_158);
x_159 = l_Lean_Expr_hasExprMVar(x_156);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_156);
if (x_160 == 0)
{
uint8_t x_161; 
lean_dec(x_156);
x_161 = l_Lean_Expr_hasExprMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasFVar(x_157);
if (x_162 == 0)
{
uint8_t x_163; lean_object* x_164; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = 1;
x_164 = lean_box(x_163);
return x_164;
}
else
{
x_8 = x_157;
goto _start;
}
}
else
{
x_8 = x_157;
goto _start;
}
}
else
{
lean_object* x_167; uint8_t x_168; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_167 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_156);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
uint8_t x_169; lean_object* x_170; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = 0;
x_170 = lean_box(x_169);
return x_170;
}
else
{
uint8_t x_171; 
x_171 = l_Lean_Expr_hasExprMVar(x_157);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_157);
if (x_172 == 0)
{
uint8_t x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = 1;
x_174 = lean_box(x_173);
return x_174;
}
else
{
x_8 = x_157;
goto _start;
}
}
else
{
x_8 = x_157;
goto _start;
}
}
}
}
else
{
lean_object* x_177; uint8_t x_178; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_177 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_156);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = 0;
x_180 = lean_box(x_179);
return x_180;
}
else
{
uint8_t x_181; 
x_181 = l_Lean_Expr_hasExprMVar(x_157);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_Expr_hasFVar(x_157);
if (x_182 == 0)
{
uint8_t x_183; lean_object* x_184; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = 1;
x_184 = lean_box(x_183);
return x_184;
}
else
{
x_8 = x_157;
goto _start;
}
}
else
{
x_8 = x_157;
goto _start;
}
}
}
}
}
case 10:
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_8, 1);
lean_inc(x_201);
lean_dec(x_8);
x_8 = x_201;
goto _start;
}
case 11:
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_8, 2);
lean_inc(x_203);
lean_dec(x_8);
x_8 = x_203;
goto _start;
}
case 12:
{
uint8_t x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_205 = l_Bool_Inhabited;
x_206 = lean_box(x_205);
x_207 = l_unreachable_x21___rarg(x_206);
return x_207;
}
default: 
{
uint8_t x_208; lean_object* x_209; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = 1;
x_209 = lean_box(x_208);
return x_209;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignmentQuick_check___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_CheckAssignmentQuick_check(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_CheckAssignmentQuick_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_CheckAssignmentQuick_check(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_LocalContext_containsFVar(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_checkAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_checkAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_69; 
x_69 = l_Lean_Expr_hasExprMVar(x_3);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasFVar(x_3);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_6 = x_73;
goto block_68;
}
}
else
{
lean_object* x_74; 
x_74 = lean_box(0);
x_6 = x_74;
goto block_68;
}
block_68:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = l_Lean_MetavarContext_getDecl(x_8, x_1);
x_14 = lean_array_get_size(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_2, x_13, x_2, x_14, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 1);
lean_dec(x_17);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_19);
lean_inc(x_8);
x_20 = l_Lean_Meta_CheckAssignmentQuick_check___main(x_16, x_18, x_8, x_19, x_13, x_1, x_2, x_3);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_5, 5);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 4);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 3);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_13);
lean_ctor_set(x_29, 3, x_2);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_29, sizeof(void*)*4 + 1, x_16);
x_30 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_10);
lean_ctor_set(x_31, 2, x_30);
lean_inc(x_3);
x_32 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_29, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_5, 3, x_38);
lean_ctor_set(x_5, 1, x_37);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_5, 3, x_43);
lean_ctor_set(x_5, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_5);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_ctor_set(x_5, 3, x_47);
x_48 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure(x_1, x_2, x_3, x_45, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_1);
lean_ctor_set(x_49, 2, x_13);
lean_ctor_set(x_49, 3, x_2);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 1, x_16);
x_50 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_8);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_10);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_3);
x_52 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_49, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_9);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_11);
lean_ctor_set(x_59, 5, x_12);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_dec(x_52);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_7);
lean_ctor_set(x_64, 1, x_8);
lean_ctor_set(x_64, 2, x_9);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_11);
lean_ctor_set(x_64, 5, x_12);
x_65 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure(x_1, x_2, x_3, x_61, x_4, x_64);
lean_dec(x_4);
lean_dec(x_2);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_3);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_Inhabited;
x_13 = lean_array_get(x_12, x_3, x_5);
x_14 = lean_array_fget(x_4, x_6);
lean_inc(x_7);
x_15 = l_Lean_Meta_isExprDefEqAux(x_13, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_25 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
x_5 = x_24;
x_6 = x_25;
x_8 = x_22;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_6);
x_8 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_7);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_7, x_10);
lean_dec(x_7);
lean_inc(x_3);
x_12 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_3, x_9, x_11);
x_13 = l_Array_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_12);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_15, x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_Expr_getAppFn___main(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(x_1, x_18, x_2, x_12, x_6, x_6, x_4, x_5);
lean_dec(x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Expr_getAppFn___main(x_3);
lean_dec(x_3);
x_21 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_22 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_21, x_12, x_6, x_20);
x_23 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(x_1, x_22, x_2, x_12, x_6, x_21, x_4, x_5);
lean_dec(x_12);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_nat_sub(x_15, x_14);
lean_dec(x_14);
lean_dec(x_15);
x_25 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_24, x_2, x_6, x_1);
x_26 = l_Lean_Expr_getAppFn___main(x_3);
lean_dec(x_3);
x_27 = l___private_Init_Lean_Meta_ExprDefEq_12__isDefEqFOApprox___main(x_25, x_26, x_2, x_12, x_24, x_6, x_4, x_5);
lean_dec(x_12);
return x_27;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_PersistentArray_empty___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_ctor_set(x_5, 5, x_10);
lean_inc(x_4);
x_19 = l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_7, x_8, x_9, x_4, x_22);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_7, x_8, x_9, x_4, x_32);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_30);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_11 = x_42;
x_12 = x_43;
goto block_18;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_11 = x_44;
x_12 = x_45;
goto block_18;
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_7, x_8, x_9, x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_61; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_48 = lean_ctor_get(x_5, 2);
x_49 = lean_ctor_get(x_5, 3);
x_50 = lean_ctor_get(x_5, 4);
x_51 = lean_ctor_get(x_5, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_52 = l_PersistentArray_empty___closed__3;
lean_inc(x_47);
lean_inc(x_46);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set(x_53, 5, x_52);
lean_inc(x_4);
x_61 = l___private_Init_Lean_Meta_ExprDefEq_13__processAssignmentFOApproxAux(x_1, x_2, x_3, x_4, x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_46, x_47, x_51, x_4, x_64);
lean_dec(x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_62);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_4, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_46, x_47, x_51, x_4, x_73);
lean_dec(x_4);
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
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_4);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_79 = x_70;
} else {
 lean_dec_ref(x_70);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_dec(x_70);
x_54 = x_81;
x_55 = x_82;
goto block_60;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_61, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_61, 1);
lean_inc(x_84);
lean_dec(x_61);
x_54 = x_83;
x_55 = x_84;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_46, x_47, x_51, x_4, x_55);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("foApprox");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_5, 4);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
x_6 = x_5;
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3;
x_36 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_35, x_4, x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_6 = x_39;
goto block_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
lean_inc(x_1);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_42 = l_Lean_Meta_Exception_toMessageData___closed__4;
x_43 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_46 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_44, x_45);
x_47 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_49 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_3);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2;
x_53 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_52, x_51, x_4, x_40);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_6 = x_54;
goto block_32;
}
}
block_32:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1(x_1, x_2, x_3, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_4);
x_11 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_3 = x_18;
x_5 = x_17;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Meta_getLocalDecl(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_LocalDecl_value_x3f(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_10; 
lean_free_object(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_10;
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_LocalDecl_value_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_16;
x_3 = x_13;
goto _start;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__simpAssignmentArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
x_5 = l_Lean_Expr_hasExprMVar(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux___main(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Meta_ExprDefEq_15__simpAssignmentArgAux___main(x_8, x_2, x_9);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_LocalContext_containsFVar(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = lean_expr_eqv(x_10, x_4);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_3 = lean_box(0);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_6, x_8);
x_12 = lean_expr_eqv(x_11, x_4);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_3 = lean_box(0);
x_5 = lean_box(0);
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
return x_12;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeMismatch");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3;
x_2 = l_Lean_Meta_isTypeCorrect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = l_Lean_Meta_instantiateMVars(x_3, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_16 == 0)
{
lean_object* x_422; 
x_422 = lean_box(0);
x_17 = x_422;
goto block_421;
}
else
{
uint8_t x_423; 
x_423 = l_Array_isEmpty___rarg(x_5);
if (x_423 == 0)
{
lean_object* x_424; 
x_424 = lean_box(0);
x_17 = x_424;
goto block_421;
}
else
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_Expr_getAppFn___main(x_14);
x_426 = lean_expr_eqv(x_425, x_1);
lean_dec(x_425);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_box(0);
x_17 = x_427;
goto block_421;
}
else
{
lean_object* x_428; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_428 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_15);
lean_dec(x_5);
return x_428;
}
}
}
block_421:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_17);
x_18 = l_Lean_Expr_mvarId_x21(x_1);
lean_inc(x_6);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_18);
x_19 = l_Lean_Meta_checkAssignment(x_18, x_5, x_14, x_6, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
if (x_16 == 0)
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_29);
lean_dec(x_5);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_mkLambda(x_5, x_32, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1(x_2, x_5, x_5, x_8, x_36);
lean_dec(x_8);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_38 = l_Lean_Meta_inferType(x_1, x_6, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_6);
lean_inc(x_34);
x_41 = l_Lean_Meta_inferType(x_34, x_6, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 1;
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 5, x_45);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_12);
lean_inc(x_42);
lean_inc(x_39);
x_47 = l_Lean_Meta_isExprDefEqAux(x_39, x_42, x_46, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_18);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_51, 4);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_47);
x_55 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_56 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_55, x_6, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_1);
x_65 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_66 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_39);
x_68 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_70 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_34);
x_72 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_42);
x_75 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_77 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_76, x_75, x_6, x_63);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_48);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_48);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_dec(x_47);
x_83 = lean_ctor_get(x_82, 4);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_48);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_87 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_86, x_6, x_82);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_48);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_96 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_39);
x_98 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_100 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_34);
x_102 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_42);
x_105 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_107 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_106, x_105, x_6, x_93);
lean_dec(x_6);
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
lean_ctor_set(x_110, 0, x_48);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_1);
x_111 = lean_ctor_get(x_47, 1);
lean_inc(x_111);
lean_dec(x_47);
x_112 = l_Lean_Meta_assignExprMVar(x_18, x_34, x_6, x_111);
lean_dec(x_6);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
lean_ctor_set(x_112, 0, x_48);
return x_112;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_48);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_48);
x_117 = !lean_is_exclusive(x_112);
if (x_117 == 0)
{
return x_112;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_112, 0);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_112);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_47);
if (x_121 == 0)
{
return x_47;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_47, 0);
x_123 = lean_ctor_get(x_47, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_47);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_10, 0);
x_126 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 1);
x_127 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 2);
x_128 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_129 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 4);
lean_inc(x_125);
lean_dec(x_10);
x_130 = 1;
x_131 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 1, x_126);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 2, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 3, x_128);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 4, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 5, x_130);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_11);
lean_ctor_set(x_132, 2, x_12);
lean_inc(x_42);
lean_inc(x_39);
x_133 = l_Lean_Meta_isExprDefEqAux(x_39, x_42, x_132, x_43);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_18);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_136, 4);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_138, sizeof(void*)*1);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_137);
x_141 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_142 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_141, x_6, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_134);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_1);
x_150 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_151 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_39);
x_153 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_155 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_156, 0, x_34);
x_157 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_42);
x_160 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_162 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_161, x_160, x_6, x_148);
lean_dec(x_6);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_134);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_1);
x_166 = lean_ctor_get(x_133, 1);
lean_inc(x_166);
lean_dec(x_133);
x_167 = l_Lean_Meta_assignExprMVar(x_18, x_34, x_6, x_166);
lean_dec(x_6);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
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
lean_ctor_set(x_170, 0, x_134);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_134);
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_173 = x_167;
} else {
 lean_dec_ref(x_167);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_1);
x_175 = lean_ctor_get(x_133, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_133, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_177 = x_133;
} else {
 lean_dec_ref(x_133);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_41);
if (x_179 == 0)
{
return x_41;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_41, 0);
x_181 = lean_ctor_get(x_41, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_41);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_38);
if (x_183 == 0)
{
return x_38;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_38, 0);
x_185 = lean_ctor_get(x_38, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_38);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_inc(x_6);
lean_inc(x_34);
x_187 = l_Lean_Meta_isTypeCorrect(x_34, x_6, x_35);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_187, 1);
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = lean_ctor_get(x_191, 4);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*1);
lean_dec(x_193);
if (x_194 == 0)
{
lean_dec(x_34);
if (x_16 == 0)
{
uint8_t x_195; lean_object* x_196; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_195 = 0;
x_196 = lean_box(x_195);
lean_ctor_set(x_187, 0, x_196);
return x_187;
}
else
{
lean_object* x_197; 
lean_free_object(x_187);
x_197 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_191);
lean_dec(x_5);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_free_object(x_187);
x_198 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8;
x_199 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_198, x_6, x_191);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_dec(x_34);
if (x_16 == 0)
{
uint8_t x_202; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_199);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_199, 0);
lean_dec(x_203);
x_204 = 0;
x_205 = lean_box(x_204);
lean_ctor_set(x_199, 0, x_205);
return x_199;
}
else
{
lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_199, 1);
lean_inc(x_206);
lean_dec(x_199);
x_207 = 0;
x_208 = lean_box(x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_199, 1);
lean_inc(x_210);
lean_dec(x_199);
x_211 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_210);
lean_dec(x_5);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_212 = lean_ctor_get(x_199, 1);
lean_inc(x_212);
lean_dec(x_199);
lean_inc(x_1);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_1);
x_214 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_215 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_216, 0, x_34);
x_217 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7;
x_219 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_218, x_217, x_6, x_212);
if (x_16 == 0)
{
uint8_t x_220; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_219, 0);
lean_dec(x_221);
x_222 = 0;
x_223 = lean_box(x_222);
lean_ctor_set(x_219, 0, x_223);
return x_219;
}
else
{
lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = 0;
x_226 = lean_box(x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_219, 1);
lean_inc(x_228);
lean_dec(x_219);
x_229 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_228);
lean_dec(x_5);
return x_229;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_187, 1);
lean_inc(x_230);
lean_dec(x_187);
x_231 = lean_ctor_get(x_230, 4);
lean_inc(x_231);
x_232 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
lean_dec(x_231);
if (x_232 == 0)
{
lean_dec(x_34);
if (x_16 == 0)
{
uint8_t x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_233 = 0;
x_234 = lean_box(x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_230);
return x_235;
}
else
{
lean_object* x_236; 
x_236 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_230);
lean_dec(x_5);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_237 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8;
x_238 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_237, x_6, x_230);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_dec(x_34);
if (x_16 == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
x_243 = 0;
x_244 = lean_box(x_243);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_238, 1);
lean_inc(x_246);
lean_dec(x_238);
x_247 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_246);
lean_dec(x_5);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
lean_dec(x_238);
lean_inc(x_1);
x_249 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_249, 0, x_1);
x_250 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_251 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_252, 0, x_34);
x_253 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7;
x_255 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_254, x_253, x_6, x_248);
if (x_16 == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = 0;
x_259 = lean_box(x_258);
if (lean_is_scalar(x_257)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_257;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_256);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_255, 1);
lean_inc(x_261);
lean_dec(x_255);
x_262 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_5, x_14, x_6, x_261);
lean_dec(x_5);
return x_262;
}
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_14);
lean_dec(x_5);
x_263 = lean_ctor_get(x_187, 1);
lean_inc(x_263);
lean_dec(x_187);
lean_inc(x_6);
lean_inc(x_1);
x_264 = l_Lean_Meta_inferType(x_1, x_6, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_6);
lean_inc(x_34);
x_267 = l_Lean_Meta_inferType(x_34, x_6, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = !lean_is_exclusive(x_10);
if (x_270 == 0)
{
uint8_t x_271; lean_object* x_272; lean_object* x_273; 
x_271 = 1;
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 5, x_271);
x_272 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_272, 0, x_10);
lean_ctor_set(x_272, 1, x_11);
lean_ctor_set(x_272, 2, x_12);
lean_inc(x_268);
lean_inc(x_265);
x_273 = l_Lean_Meta_isExprDefEqAux(x_265, x_268, x_272, x_269);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
if (x_275 == 0)
{
uint8_t x_276; 
lean_dec(x_18);
x_276 = !lean_is_exclusive(x_273);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_277 = lean_ctor_get(x_273, 1);
x_278 = lean_ctor_get(x_273, 0);
lean_dec(x_278);
x_279 = lean_ctor_get(x_277, 4);
lean_inc(x_279);
x_280 = lean_ctor_get_uint8(x_279, sizeof(void*)*1);
lean_dec(x_279);
if (x_280 == 0)
{
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
return x_273;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_free_object(x_273);
x_281 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_282 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_281, x_6, x_277);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_282);
if (x_285 == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_282, 0);
lean_dec(x_286);
lean_ctor_set(x_282, 0, x_274);
return x_282;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
lean_dec(x_282);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_274);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_289 = lean_ctor_get(x_282, 1);
lean_inc(x_289);
lean_dec(x_282);
x_290 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_290, 0, x_1);
x_291 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_292 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_293, 0, x_265);
x_294 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_296 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_297, 0, x_34);
x_298 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_291);
x_300 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_300, 0, x_268);
x_301 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_303 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_302, x_301, x_6, x_289);
lean_dec(x_6);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_303, 0);
lean_dec(x_305);
lean_ctor_set(x_303, 0, x_274);
return x_303;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_274);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_308 = lean_ctor_get(x_273, 1);
lean_inc(x_308);
lean_dec(x_273);
x_309 = lean_ctor_get(x_308, 4);
lean_inc(x_309);
x_310 = lean_ctor_get_uint8(x_309, sizeof(void*)*1);
lean_dec(x_309);
if (x_310 == 0)
{
lean_object* x_311; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_274);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_312 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_313 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_312, x_6, x_308);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_317 = x_313;
} else {
 lean_dec_ref(x_313);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_274);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
lean_dec(x_313);
x_320 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_320, 0, x_1);
x_321 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_322 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_323, 0, x_265);
x_324 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_326 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_34);
x_328 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_321);
x_330 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_330, 0, x_268);
x_331 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_333 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_332, x_331, x_6, x_319);
lean_dec(x_6);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_274);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_1);
x_337 = lean_ctor_get(x_273, 1);
lean_inc(x_337);
lean_dec(x_273);
x_338 = l_Lean_Meta_assignExprMVar(x_18, x_34, x_6, x_337);
lean_dec(x_6);
if (lean_obj_tag(x_338) == 0)
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 0);
lean_dec(x_340);
lean_ctor_set(x_338, 0, x_274);
return x_338;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_274);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
else
{
uint8_t x_343; 
lean_dec(x_274);
x_343 = !lean_is_exclusive(x_338);
if (x_343 == 0)
{
return x_338;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_338, 0);
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_338);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_1);
x_347 = !lean_is_exclusive(x_273);
if (x_347 == 0)
{
return x_273;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_273, 0);
x_349 = lean_ctor_get(x_273, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_273);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; uint8_t x_352; uint8_t x_353; uint8_t x_354; uint8_t x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_351 = lean_ctor_get(x_10, 0);
x_352 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 1);
x_353 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 2);
x_354 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_355 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 4);
lean_inc(x_351);
lean_dec(x_10);
x_356 = 1;
x_357 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set_uint8(x_357, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_357, sizeof(void*)*1 + 1, x_352);
lean_ctor_set_uint8(x_357, sizeof(void*)*1 + 2, x_353);
lean_ctor_set_uint8(x_357, sizeof(void*)*1 + 3, x_354);
lean_ctor_set_uint8(x_357, sizeof(void*)*1 + 4, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*1 + 5, x_356);
x_358 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_11);
lean_ctor_set(x_358, 2, x_12);
lean_inc(x_268);
lean_inc(x_265);
x_359 = l_Lean_Meta_isExprDefEqAux(x_265, x_268, x_358, x_269);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_unbox(x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
lean_dec(x_18);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
x_364 = lean_ctor_get(x_362, 4);
lean_inc(x_364);
x_365 = lean_ctor_get_uint8(x_364, sizeof(void*)*1);
lean_dec(x_364);
if (x_365 == 0)
{
lean_object* x_366; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_363)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_363;
}
lean_ctor_set(x_366, 0, x_360);
lean_ctor_set(x_366, 1, x_362);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
lean_dec(x_363);
x_367 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3;
x_368 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_367, x_6, x_362);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_1);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_360);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_374 = lean_ctor_get(x_368, 1);
lean_inc(x_374);
lean_dec(x_368);
x_375 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_375, 0, x_1);
x_376 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6;
x_377 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_378, 0, x_265);
x_379 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7;
x_381 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_382, 0, x_34);
x_383 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_376);
x_385 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_385, 0, x_268);
x_386 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2;
x_388 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_387, x_386, x_6, x_374);
lean_dec(x_6);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_390 = x_388;
} else {
 lean_dec_ref(x_388);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_360);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_1);
x_392 = lean_ctor_get(x_359, 1);
lean_inc(x_392);
lean_dec(x_359);
x_393 = l_Lean_Meta_assignExprMVar(x_18, x_34, x_6, x_392);
lean_dec(x_6);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_360);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_360);
x_397 = lean_ctor_get(x_393, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_393, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_399 = x_393;
} else {
 lean_dec_ref(x_393);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_1);
x_401 = lean_ctor_get(x_359, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_359, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_403 = x_359;
} else {
 lean_dec_ref(x_359);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_267);
if (x_405 == 0)
{
return x_267;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_267, 0);
x_407 = lean_ctor_get(x_267, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_267);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_264);
if (x_409 == 0)
{
return x_264;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_264, 0);
x_411 = lean_ctor_get(x_264, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_264);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
}
}
else
{
uint8_t x_413; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_413 = !lean_is_exclusive(x_33);
if (x_413 == 0)
{
return x_33;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_33, 0);
x_415 = lean_ctor_get(x_33, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_33);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_19);
if (x_417 == 0)
{
return x_19;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_19, 0);
x_419 = lean_ctor_get(x_19, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_19);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_8);
x_429 = lean_ctor_get(x_6, 0);
lean_inc(x_429);
x_430 = lean_array_fget(x_5, x_4);
lean_inc(x_6);
x_431 = l___private_Init_Lean_Meta_ExprDefEq_16__simpAssignmentArg(x_430, x_6, x_7);
if (lean_obj_tag(x_431) == 0)
{
uint8_t x_432; 
x_432 = !lean_is_exclusive(x_431);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_431, 0);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_inc(x_5);
x_435 = lean_array_fset(x_5, x_4, x_433);
if (lean_obj_tag(x_433) == 1)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = lean_ctor_get(x_433, 0);
lean_inc(x_436);
x_437 = lean_array_get_size(x_435);
x_438 = lean_nat_dec_le(x_4, x_437);
if (x_438 == 0)
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_unsigned_to_nat(0u);
x_440 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2(x_4, x_5, lean_box(0), x_433, x_435, x_437, x_439);
lean_dec(x_437);
lean_dec(x_433);
lean_dec(x_5);
if (x_440 == 0)
{
lean_object* x_441; uint8_t x_442; 
x_441 = lean_ctor_get(x_2, 1);
x_442 = l_Lean_LocalContext_contains(x_441, x_436);
lean_dec(x_436);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; 
lean_free_object(x_431);
lean_dec(x_429);
x_443 = lean_unsigned_to_nat(1u);
x_444 = lean_nat_add(x_4, x_443);
lean_dec(x_4);
x_4 = x_444;
x_5 = x_435;
x_7 = x_434;
goto _start;
}
else
{
uint8_t x_446; 
x_446 = lean_ctor_get_uint8(x_429, sizeof(void*)*1 + 2);
if (x_446 == 0)
{
uint8_t x_447; 
lean_dec(x_4);
x_447 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_447 == 0)
{
uint8_t x_448; lean_object* x_449; 
lean_dec(x_435);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_448 = 0;
x_449 = lean_box(x_448);
lean_ctor_set(x_431, 0, x_449);
return x_431;
}
else
{
lean_object* x_450; 
lean_free_object(x_431);
x_450 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_435, x_3, x_6, x_434);
lean_dec(x_435);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_free_object(x_431);
lean_dec(x_429);
x_451 = lean_unsigned_to_nat(1u);
x_452 = lean_nat_add(x_4, x_451);
lean_dec(x_4);
x_4 = x_452;
x_5 = x_435;
x_7 = x_434;
goto _start;
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_436);
lean_dec(x_4);
x_454 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_454 == 0)
{
uint8_t x_455; lean_object* x_456; 
lean_dec(x_435);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_455 = 0;
x_456 = lean_box(x_455);
lean_ctor_set(x_431, 0, x_456);
return x_431;
}
else
{
lean_object* x_457; 
lean_free_object(x_431);
x_457 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_435, x_3, x_6, x_434);
lean_dec(x_435);
return x_457;
}
}
}
else
{
lean_object* x_458; uint8_t x_459; 
lean_dec(x_437);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3(x_4, x_5, lean_box(0), x_433, lean_box(0), x_435, x_4, x_458);
lean_dec(x_433);
lean_dec(x_5);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; 
x_460 = lean_ctor_get(x_2, 1);
x_461 = l_Lean_LocalContext_contains(x_460, x_436);
lean_dec(x_436);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; 
lean_free_object(x_431);
lean_dec(x_429);
x_462 = lean_unsigned_to_nat(1u);
x_463 = lean_nat_add(x_4, x_462);
lean_dec(x_4);
x_4 = x_463;
x_5 = x_435;
x_7 = x_434;
goto _start;
}
else
{
uint8_t x_465; 
x_465 = lean_ctor_get_uint8(x_429, sizeof(void*)*1 + 2);
if (x_465 == 0)
{
uint8_t x_466; 
lean_dec(x_4);
x_466 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_466 == 0)
{
uint8_t x_467; lean_object* x_468; 
lean_dec(x_435);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_467 = 0;
x_468 = lean_box(x_467);
lean_ctor_set(x_431, 0, x_468);
return x_431;
}
else
{
lean_object* x_469; 
lean_free_object(x_431);
x_469 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_435, x_3, x_6, x_434);
lean_dec(x_435);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_free_object(x_431);
lean_dec(x_429);
x_470 = lean_unsigned_to_nat(1u);
x_471 = lean_nat_add(x_4, x_470);
lean_dec(x_4);
x_4 = x_471;
x_5 = x_435;
x_7 = x_434;
goto _start;
}
}
}
else
{
uint8_t x_473; 
lean_dec(x_436);
lean_dec(x_4);
x_473 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_473 == 0)
{
uint8_t x_474; lean_object* x_475; 
lean_dec(x_435);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_474 = 0;
x_475 = lean_box(x_474);
lean_ctor_set(x_431, 0, x_475);
return x_431;
}
else
{
lean_object* x_476; 
lean_free_object(x_431);
x_476 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_435, x_3, x_6, x_434);
lean_dec(x_435);
return x_476;
}
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_433);
lean_dec(x_5);
lean_dec(x_4);
x_477 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_477 == 0)
{
uint8_t x_478; lean_object* x_479; 
lean_dec(x_435);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_478 = 0;
x_479 = lean_box(x_478);
lean_ctor_set(x_431, 0, x_479);
return x_431;
}
else
{
lean_object* x_480; 
lean_free_object(x_431);
x_480 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_435, x_3, x_6, x_434);
lean_dec(x_435);
return x_480;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_431, 0);
x_482 = lean_ctor_get(x_431, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_431);
lean_inc(x_481);
lean_inc(x_5);
x_483 = lean_array_fset(x_5, x_4, x_481);
if (lean_obj_tag(x_481) == 1)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_484 = lean_ctor_get(x_481, 0);
lean_inc(x_484);
x_485 = lean_array_get_size(x_483);
x_486 = lean_nat_dec_le(x_4, x_485);
if (x_486 == 0)
{
lean_object* x_487; uint8_t x_488; 
x_487 = lean_unsigned_to_nat(0u);
x_488 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2(x_4, x_5, lean_box(0), x_481, x_483, x_485, x_487);
lean_dec(x_485);
lean_dec(x_481);
lean_dec(x_5);
if (x_488 == 0)
{
lean_object* x_489; uint8_t x_490; 
x_489 = lean_ctor_get(x_2, 1);
x_490 = l_Lean_LocalContext_contains(x_489, x_484);
lean_dec(x_484);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; 
lean_dec(x_429);
x_491 = lean_unsigned_to_nat(1u);
x_492 = lean_nat_add(x_4, x_491);
lean_dec(x_4);
x_4 = x_492;
x_5 = x_483;
x_7 = x_482;
goto _start;
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_429, sizeof(void*)*1 + 2);
if (x_494 == 0)
{
uint8_t x_495; 
lean_dec(x_4);
x_495 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_495 == 0)
{
uint8_t x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_496 = 0;
x_497 = lean_box(x_496);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_482);
return x_498;
}
else
{
lean_object* x_499; 
x_499 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_483, x_3, x_6, x_482);
lean_dec(x_483);
return x_499;
}
}
else
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_429);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_add(x_4, x_500);
lean_dec(x_4);
x_4 = x_501;
x_5 = x_483;
x_7 = x_482;
goto _start;
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_484);
lean_dec(x_4);
x_503 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_503 == 0)
{
uint8_t x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_504 = 0;
x_505 = lean_box(x_504);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_482);
return x_506;
}
else
{
lean_object* x_507; 
x_507 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_483, x_3, x_6, x_482);
lean_dec(x_483);
return x_507;
}
}
}
else
{
lean_object* x_508; uint8_t x_509; 
lean_dec(x_485);
x_508 = lean_unsigned_to_nat(0u);
x_509 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3(x_4, x_5, lean_box(0), x_481, lean_box(0), x_483, x_4, x_508);
lean_dec(x_481);
lean_dec(x_5);
if (x_509 == 0)
{
lean_object* x_510; uint8_t x_511; 
x_510 = lean_ctor_get(x_2, 1);
x_511 = l_Lean_LocalContext_contains(x_510, x_484);
lean_dec(x_484);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; 
lean_dec(x_429);
x_512 = lean_unsigned_to_nat(1u);
x_513 = lean_nat_add(x_4, x_512);
lean_dec(x_4);
x_4 = x_513;
x_5 = x_483;
x_7 = x_482;
goto _start;
}
else
{
uint8_t x_515; 
x_515 = lean_ctor_get_uint8(x_429, sizeof(void*)*1 + 2);
if (x_515 == 0)
{
uint8_t x_516; 
lean_dec(x_4);
x_516 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_516 == 0)
{
uint8_t x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_517 = 0;
x_518 = lean_box(x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_482);
return x_519;
}
else
{
lean_object* x_520; 
x_520 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_483, x_3, x_6, x_482);
lean_dec(x_483);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_429);
x_521 = lean_unsigned_to_nat(1u);
x_522 = lean_nat_add(x_4, x_521);
lean_dec(x_4);
x_4 = x_522;
x_5 = x_483;
x_7 = x_482;
goto _start;
}
}
}
else
{
uint8_t x_524; 
lean_dec(x_484);
lean_dec(x_4);
x_524 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_524 == 0)
{
uint8_t x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_525 = 0;
x_526 = lean_box(x_525);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_482);
return x_527;
}
else
{
lean_object* x_528; 
x_528 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_483, x_3, x_6, x_482);
lean_dec(x_483);
return x_528;
}
}
}
}
else
{
uint8_t x_529; 
lean_dec(x_481);
lean_dec(x_5);
lean_dec(x_4);
x_529 = lean_ctor_get_uint8(x_429, sizeof(void*)*1);
lean_dec(x_429);
if (x_529 == 0)
{
uint8_t x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_530 = 0;
x_531 = lean_box(x_530);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_482);
return x_532;
}
else
{
lean_object* x_533; 
x_533 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main(x_1, x_483, x_3, x_6, x_482);
lean_dec(x_483);
return x_533;
}
}
}
}
else
{
uint8_t x_534; 
lean_dec(x_429);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_534 = !lean_is_exclusive(x_431);
if (x_534 == 0)
{
return x_431;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_431, 0);
x_536 = lean_ctor_get(x_431, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_431);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_getAppFn___main(x_1);
x_6 = l_Lean_Expr_mvarId_x21(x_5);
x_7 = l_Lean_Meta_getMVarDecl(x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_10);
x_12 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_13, x_15);
x_17 = l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main(x_5, x_8, x_2, x_10, x_16, x_3, x_9);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 1;
x_7 = l_Lean_Meta_getConstAux(x_5, x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isListLevelDefEqAux___main(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Bool_toLBool(x_8);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_unbox(x_11);
lean_dec(x_11);
x_14 = l_Bool_toLBool(x_13);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delta");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldLeft");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5;
x_25 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_24, x_4, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = l_Bool_toLBool(x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = l_Bool_toLBool(x_37);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4;
x_48 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_47, x_46, x_4, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
x_54 = l_Bool_toLBool(x_53);
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_59 = l_Bool_toLBool(x_58);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldRight");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3;
x_25 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_24, x_4, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = l_Bool_toLBool(x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = l_Bool_toLBool(x_37);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2;
x_48 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_47, x_46, x_4, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
x_54 = l_Bool_toLBool(x_53);
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_59 = l_Bool_toLBool(x_58);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldLeftRight");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3;
x_25 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_24, x_4, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = l_Bool_toLBool(x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = l_Bool_toLBool(x_37);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2;
x_48 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_47, x_46, x_4, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_isExprDefEqAux(x_2, x_3, x_4, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
x_54 = l_Bool_toLBool(x_53);
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_59 = l_Bool_toLBool(x_58);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_constLevels_x21(x_1);
x_9 = l_Lean_Expr_constLevels_x21(x_2);
x_10 = l_Lean_Meta_isListLevelDefEqAux___main(x_8, x_9, x_4, x_5);
return x_10;
}
}
}
lean_object* _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heuristic failed ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Name_append___main(x_11, x_1);
x_13 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_12, x_5, x_6);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(x_4);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3;
x_25 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_Exception_toMessageData___closed__51;
x_27 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_3);
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1, x_29, x_5, x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(x_4);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_8);
x_10 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_11, x_13);
x_15 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_8);
lean_inc(x_15);
x_16 = lean_mk_array(x_15, x_10);
x_17 = lean_nat_sub(x_15, x_12);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_16, x_17);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___boxed), 5, 3);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1___boxed), 5, 2);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_4);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___boxed), 6, 3);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_36; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 5);
x_27 = l_PersistentArray_empty___closed__3;
lean_inc(x_25);
lean_inc(x_24);
lean_ctor_set(x_7, 5, x_27);
lean_inc(x_6);
x_36 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_21, x_22, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_39);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_49);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_46, 0);
lean_dec(x_56);
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_dec(x_46);
x_28 = x_59;
x_29 = x_60;
goto block_35;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_dec(x_36);
x_28 = x_61;
x_29 = x_62;
goto block_35;
}
block_35:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_29);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_78; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get(x_7, 1);
x_65 = lean_ctor_get(x_7, 2);
x_66 = lean_ctor_get(x_7, 3);
x_67 = lean_ctor_get(x_7, 4);
x_68 = lean_ctor_get(x_7, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_7);
x_69 = l_PersistentArray_empty___closed__3;
lean_inc(x_64);
lean_inc(x_63);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
lean_ctor_set(x_70, 4, x_67);
lean_ctor_set(x_70, 5, x_69);
lean_inc(x_6);
x_78 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_21, x_22, x_6, x_70);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_81);
lean_dec(x_6);
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
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_dec(x_78);
x_87 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_90);
lean_dec(x_6);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_6);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_dec(x_87);
x_71 = x_98;
x_72 = x_99;
goto block_77;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_71 = x_100;
x_72 = x_101;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_72);
lean_dec(x_6);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_8);
x_10 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_11, x_13);
x_15 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_8);
lean_inc(x_15);
x_16 = lean_mk_array(x_15, x_10);
x_17 = lean_nat_sub(x_15, x_12);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_16, x_17);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___boxed), 5, 3);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1___boxed), 5, 2);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_4);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___boxed), 6, 3);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_36; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 5);
x_27 = l_PersistentArray_empty___closed__3;
lean_inc(x_25);
lean_inc(x_24);
lean_ctor_set(x_7, 5, x_27);
lean_inc(x_6);
x_36 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_21, x_22, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_39);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_49);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_46, 0);
lean_dec(x_56);
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_dec(x_46);
x_28 = x_59;
x_29 = x_60;
goto block_35;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_dec(x_36);
x_28 = x_61;
x_29 = x_62;
goto block_35;
}
block_35:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_24, x_25, x_26, x_6, x_29);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_78; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get(x_7, 1);
x_65 = lean_ctor_get(x_7, 2);
x_66 = lean_ctor_get(x_7, 3);
x_67 = lean_ctor_get(x_7, 4);
x_68 = lean_ctor_get(x_7, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_7);
x_69 = l_PersistentArray_empty___closed__3;
lean_inc(x_64);
lean_inc(x_63);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
lean_ctor_set(x_70, 4, x_67);
lean_ctor_set(x_70, 5, x_69);
lean_inc(x_6);
x_78 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_21, x_22, x_6, x_70);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_81);
lean_dec(x_6);
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
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_dec(x_78);
x_87 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_6, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_90);
lean_dec(x_6);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_6);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_dec(x_87);
x_71 = x_98;
x_72 = x_99;
goto block_77;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_71 = x_100;
x_72 = x_101;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_63, x_64, x_68, x_6, x_72);
lean_dec(x_6);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_176; uint8_t x_177; 
x_5 = l_Lean_Expr_getAppFn___main(x_1);
x_6 = l_Lean_Expr_getAppFn___main(x_2);
x_176 = lean_ctor_get(x_4, 4);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_176, sizeof(void*)*1);
lean_dec(x_176);
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = 0;
x_7 = x_178;
x_8 = x_4;
goto block_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_179 = l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1;
x_180 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_179, x_3, x_4);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_unbox(x_181);
lean_dec(x_181);
x_7 = x_183;
x_8 = x_182;
goto block_175;
}
block_175:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_13 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_13);
x_14 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_15 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1(x_1, x_2, x_5, x_6, x_14, x_3, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 4);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_12);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_12);
lean_ctor_set(x_16, 4, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_16, 2);
x_28 = lean_ctor_get(x_16, 3);
x_29 = lean_ctor_get(x_16, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_31 = x_17;
} else {
 lean_dec_ref(x_17);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 1);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_12);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_29);
lean_ctor_set(x_15, 1, x_33);
return x_15;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_16, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_40 = x_16;
} else {
 lean_dec_ref(x_16);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_42 = x_17;
} else {
 lean_dec_ref(x_17);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_12);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 4);
lean_inc(x_47);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_15, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 4);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_12);
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_12);
lean_ctor_set(x_46, 4, x_54);
return x_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
x_57 = lean_ctor_get(x_46, 2);
x_58 = lean_ctor_get(x_46, 3);
x_59 = lean_ctor_get(x_46, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_12);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_57);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_59);
lean_ctor_set(x_15, 1, x_63);
return x_15;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_15, 0);
lean_inc(x_64);
lean_dec(x_15);
x_65 = lean_ctor_get(x_46, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_46, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_46, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_46, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_46, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_70 = x_46;
} else {
 lean_dec_ref(x_46);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_72 = x_47;
} else {
 lean_dec_ref(x_47);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_12);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 6, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_66);
lean_ctor_set(x_74, 2, x_67);
lean_ctor_set(x_74, 3, x_68);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_77 = lean_ctor_get(x_10, 0);
lean_inc(x_77);
lean_dec(x_10);
x_78 = 0;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
lean_ctor_set(x_8, 4, x_79);
x_80 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_81 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1(x_1, x_2, x_5, x_6, x_80, x_3, x_8);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 lean_ctor_release(x_82, 5);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 1, 1);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_91)) {
 x_95 = lean_alloc_ctor(0, 6, 0);
} else {
 x_95 = x_91;
}
lean_ctor_set(x_95, 0, x_86);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_88);
lean_ctor_set(x_95, 3, x_89);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_95, 5, x_90);
if (lean_is_scalar(x_85)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_85;
}
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_81, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_100 = x_81;
} else {
 lean_dec_ref(x_81);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 5);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_98, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 1, 1);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_106)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_106;
}
lean_ctor_set(x_110, 0, x_101);
lean_ctor_set(x_110, 1, x_102);
lean_ctor_set(x_110, 2, x_103);
lean_ctor_set(x_110, 3, x_104);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_105);
if (lean_is_scalar(x_100)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_100;
}
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_112 = lean_ctor_get(x_8, 4);
x_113 = lean_ctor_get(x_8, 0);
x_114 = lean_ctor_get(x_8, 1);
x_115 = lean_ctor_get(x_8, 2);
x_116 = lean_ctor_get(x_8, 3);
x_117 = lean_ctor_get(x_8, 5);
lean_inc(x_117);
lean_inc(x_112);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_8);
x_118 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
x_121 = 0;
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 1, 1);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
x_123 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_114);
lean_ctor_set(x_123, 2, x_115);
lean_ctor_set(x_123, 3, x_116);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set(x_123, 5, x_117);
x_124 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
x_125 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1(x_1, x_2, x_5, x_6, x_124, x_3, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_129 = x_125;
} else {
 lean_dec_ref(x_125);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_126, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_126, 5);
lean_inc(x_134);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 lean_ctor_release(x_126, 5);
 x_135 = x_126;
} else {
 lean_dec_ref(x_126);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_118);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 6, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_132);
lean_ctor_set(x_139, 3, x_133);
lean_ctor_set(x_139, 4, x_138);
lean_ctor_set(x_139, 5, x_134);
if (lean_is_scalar(x_129)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_129;
}
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_125, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_144 = x_125;
} else {
 lean_dec_ref(x_125);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_141, 5);
lean_inc(x_149);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 lean_ctor_release(x_141, 5);
 x_150 = x_141;
} else {
 lean_dec_ref(x_141);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_142, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_152 = x_142;
} else {
 lean_dec_ref(x_142);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 1, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_118);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set(x_154, 4, x_153);
lean_ctor_set(x_154, 5, x_149);
if (lean_is_scalar(x_144)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_144;
}
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = l___private_Init_Lean_Trace_2__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_8);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2;
lean_inc(x_3);
x_160 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__2(x_1, x_2, x_5, x_6, x_159, x_3, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l___private_Init_Lean_Trace_1__addNode___at_Lean_Meta_check___spec__2(x_157, x_159, x_3, x_162);
lean_dec(x_3);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 1);
lean_inc(x_169);
lean_dec(x_160);
x_170 = l___private_Init_Lean_Trace_1__addNode___at_Lean_Meta_check___spec__2(x_157, x_159, x_3, x_169);
lean_dec(x_3);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
lean_dec(x_172);
lean_ctor_set_tag(x_170, 1);
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_25__unfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_3(x_3, x_11, x_4, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_25__unfold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_25__unfold___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_26__unfoldBothDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Meta_ExprDefEq_20__isListLevelDefEq(x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_12; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_16 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_2, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_19 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_4, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_1, x_2, x_30, x_4, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_4, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_1, x_37, x_3, x_4, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight(x_1, x_37, x_43, x_4, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_12, 0);
lean_dec(x_54);
x_55 = 1;
x_56 = lean_box(x_55);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_dec(x_12);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
}
default: 
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_5);
return x_70;
}
}
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_4) == 4)
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 2;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 2;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_ConstantInfo_name(x_2);
x_23 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_22, x_3, x_21, x_5, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol(x_29, x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_31, x_29, x_4, x_5, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l___private_Init_Lean_Meta_ExprDefEq_27__sameHeadSymbol(x_3, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_3);
x_39 = l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight(x_31, x_29, x_37, x_5, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_29);
x_40 = l_Lean_ConstantInfo_name(x_2);
x_41 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_40, x_3, x_37, x_5, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_46 = l_Lean_ConstantInfo_name(x_1);
x_47 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_46, x_29, x_4, x_5, x_28);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasExprMVar(x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasExprMVar(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_ConstantInfo_hints(x_1);
x_10 = l_Lean_ConstantInfo_hints(x_2);
x_11 = l_Lean_ReducibilityHints_lt(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_ReducibilityHints_lt(x_10, x_9);
lean_dec(x_9);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_ConstantInfo_name(x_2);
x_21 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_20, x_3, x_19, x_5, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_3);
x_26 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_ConstantInfo_name(x_1);
x_33 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_32, x_31, x_4, x_5, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; 
x_38 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = l___private_Init_Lean_Meta_ExprDefEq_28__unfoldComparingHeadsDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 5);
lean_dec(x_7);
x_9 = 2;
x_10 = l_Lean_Meta_TransparencyMode_beq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = l_Lean_ConstantInfo_name(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_12);
x_13 = l_Lean_isReducible(x_12, x_11);
x_14 = l_Lean_ConstantInfo_name(x_2);
lean_inc(x_14);
x_15 = l_Lean_isReducible(x_12, x_14);
if (x_13 == 0)
{
lean_object* x_43; 
lean_dec(x_11);
x_43 = lean_box(0);
x_16 = x_43;
goto block_42;
}
else
{
if (x_15 == 0)
{
lean_object* x_44; 
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_3);
x_44 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_11);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_11, x_49, x_4, x_5, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_11);
x_55 = lean_box(0);
x_16 = x_55;
goto block_42;
}
}
block_42:
{
lean_dec(x_16);
if (x_13 == 0)
{
if (x_15 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_14, x_3, x_23, x_5, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
if (x_10 == 0)
{
lean_object* x_29; 
lean_dec(x_14);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
else
{
if (x_15 == 0)
{
lean_object* x_30; 
lean_dec(x_14);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_30;
}
else
{
lean_object* x_31; 
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_14, x_3, x_36, x_5, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
}
else
{
lean_object* x_56; 
x_56 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_56;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_8);
x_9 = l_Lean_Environment_isProjectionFn(x_7, x_8);
x_10 = l_Lean_ConstantInfo_name(x_2);
lean_inc(x_10);
x_11 = l_Lean_Environment_isProjectionFn(x_7, x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_5);
lean_inc(x_3);
x_13 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_3, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_8, x_18, x_4, x_5, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_24; 
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Init_Lean_Meta_ExprDefEq_29__unfoldDefEq(x_1, x_2, x_3, x_4, x_5, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_10, x_3, x_29, x_5, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_10);
x_35 = l___private_Init_Lean_Meta_ExprDefEq_30__unfoldReducibeDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_35;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_32__isDefEqDelta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Expr_getAppFn___main(x_1);
x_6 = l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate(x_5, x_3, x_4);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_getAppFn___main(x_2);
x_10 = l___private_Init_Lean_Meta_ExprDefEq_19__isDeltaCandidate(x_9, x_3, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 2;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 2;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_3);
x_22 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_2, x_3, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = 2;
x_27 = lean_box(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = 2;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lean_ConstantInfo_name(x_21);
lean_dec(x_21);
x_35 = l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight(x_34, x_1, x_33, x_3, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_dec(x_10);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
lean_inc(x_3);
x_43 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_1, x_3, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = 2;
x_48 = lean_box(x_47);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = l_Lean_ConstantInfo_name(x_42);
lean_dec(x_42);
x_56 = l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft(x_55, x_54, x_2, x_3, x_53);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_43);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_dec(x_10);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_ctor_get(x_40, 0);
lean_inc(x_63);
lean_dec(x_40);
x_64 = l_Lean_ConstantInfo_name(x_62);
x_65 = l_Lean_ConstantInfo_name(x_63);
x_66 = lean_name_eq(x_64, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
x_67 = l___private_Init_Lean_Meta_ExprDefEq_31__unfoldNonProjFnDefEq(x_62, x_63, x_1, x_2, x_3, x_61);
lean_dec(x_63);
lean_dec(x_62);
return x_67;
}
else
{
lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_62);
x_68 = l___private_Init_Lean_Meta_ExprDefEq_26__unfoldBothDefEq(x_64, x_1, x_2, x_3, x_61);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_10);
if (x_69 == 0)
{
return x_10;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_10, 0);
x_71 = lean_ctor_get(x_10, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_10);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_6);
if (x_73 == 0)
{
return x_6;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_6);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_is_expr_assigned(x_5, x_4);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_isSyntheticExprMVar(x_4, x_2, x_3);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 1;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_36__etaEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Lean_Expr_9__etaExpandedAux___main(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_expr_eqv(x_6, x_2);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_36__etaEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Meta_ExprDefEq_36__etaEq(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_37__isLetFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_LocalDecl_isLet(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lean_LocalDecl_isLet(x_9);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_407; 
switch (lean_obj_tag(x_1)) {
case 1:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_1, 0);
lean_inc(x_431);
lean_dec(x_1);
x_432 = lean_ctor_get(x_2, 0);
lean_inc(x_432);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_431);
x_433 = l___private_Init_Lean_Meta_ExprDefEq_37__isLetFVar(x_431, x_3, x_4);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_unbox(x_434);
lean_dec(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_433, 1);
lean_inc(x_436);
lean_dec(x_433);
lean_inc(x_432);
x_437 = l___private_Init_Lean_Meta_ExprDefEq_37__isLetFVar(x_432, x_3, x_436);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; uint8_t x_439; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_unbox(x_438);
lean_dec(x_438);
if (x_439 == 0)
{
uint8_t x_440; 
x_440 = !lean_is_exclusive(x_437);
if (x_440 == 0)
{
lean_object* x_441; uint8_t x_442; uint8_t x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_437, 0);
lean_dec(x_441);
x_442 = lean_name_eq(x_431, x_432);
lean_dec(x_432);
lean_dec(x_431);
x_443 = l_Bool_toLBool(x_442);
x_444 = lean_box(x_443);
lean_ctor_set(x_437, 0, x_444);
return x_437;
}
else
{
lean_object* x_445; uint8_t x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; 
x_445 = lean_ctor_get(x_437, 1);
lean_inc(x_445);
lean_dec(x_437);
x_446 = lean_name_eq(x_431, x_432);
lean_dec(x_432);
lean_dec(x_431);
x_447 = l_Bool_toLBool(x_446);
x_448 = lean_box(x_447);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_445);
return x_449;
}
}
else
{
uint8_t x_450; 
lean_dec(x_432);
lean_dec(x_431);
x_450 = !lean_is_exclusive(x_437);
if (x_450 == 0)
{
lean_object* x_451; uint8_t x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_437, 0);
lean_dec(x_451);
x_452 = 2;
x_453 = lean_box(x_452);
lean_ctor_set(x_437, 0, x_453);
return x_437;
}
else
{
lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_ctor_get(x_437, 1);
lean_inc(x_454);
lean_dec(x_437);
x_455 = 2;
x_456 = lean_box(x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_454);
return x_457;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_432);
lean_dec(x_431);
x_458 = !lean_is_exclusive(x_437);
if (x_458 == 0)
{
return x_437;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_437, 0);
x_460 = lean_ctor_get(x_437, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_437);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_3);
x_462 = !lean_is_exclusive(x_433);
if (x_462 == 0)
{
lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_433, 0);
lean_dec(x_463);
x_464 = 2;
x_465 = lean_box(x_464);
lean_ctor_set(x_433, 0, x_465);
return x_433;
}
else
{
lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_433, 1);
lean_inc(x_466);
lean_dec(x_433);
x_467 = 2;
x_468 = lean_box(x_467);
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_466);
return x_469;
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_3);
x_470 = !lean_is_exclusive(x_433);
if (x_470 == 0)
{
return x_433;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_433, 0);
x_472 = lean_ctor_get(x_433, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_433);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
case 10:
{
lean_object* x_474; 
x_474 = lean_ctor_get(x_2, 1);
lean_inc(x_474);
lean_dec(x_2);
x_2 = x_474;
goto _start;
}
default: 
{
lean_object* x_476; 
x_476 = lean_box(0);
x_5 = x_476;
goto block_406;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_1, 0);
lean_inc(x_477);
lean_dec(x_1);
x_478 = lean_ctor_get(x_2, 0);
lean_inc(x_478);
lean_dec(x_2);
x_479 = l_Lean_Meta_isLevelDefEqAux___main(x_477, x_478, x_3, x_4);
lean_dec(x_3);
if (lean_obj_tag(x_479) == 0)
{
uint8_t x_480; 
x_480 = !lean_is_exclusive(x_479);
if (x_480 == 0)
{
lean_object* x_481; uint8_t x_482; uint8_t x_483; lean_object* x_484; 
x_481 = lean_ctor_get(x_479, 0);
x_482 = lean_unbox(x_481);
lean_dec(x_481);
x_483 = l_Bool_toLBool(x_482);
x_484 = lean_box(x_483);
lean_ctor_set(x_479, 0, x_484);
return x_479;
}
else
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_485 = lean_ctor_get(x_479, 0);
x_486 = lean_ctor_get(x_479, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_479);
x_487 = lean_unbox(x_485);
lean_dec(x_485);
x_488 = l_Bool_toLBool(x_487);
x_489 = lean_box(x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_486);
return x_490;
}
}
else
{
uint8_t x_491; 
x_491 = !lean_is_exclusive(x_479);
if (x_491 == 0)
{
return x_479;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_479, 0);
x_493 = lean_ctor_get(x_479, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_479);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
case 10:
{
lean_object* x_495; 
x_495 = lean_ctor_get(x_2, 1);
lean_inc(x_495);
lean_dec(x_2);
x_2 = x_495;
goto _start;
}
default: 
{
lean_object* x_497; 
x_497 = lean_box(0);
x_5 = x_497;
goto block_406;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_498; 
x_498 = lean_box(0);
x_407 = x_498;
goto block_430;
}
case 10:
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_2, 1);
lean_inc(x_499);
lean_dec(x_2);
x_2 = x_499;
goto _start;
}
default: 
{
lean_object* x_501; 
x_501 = lean_box(0);
x_5 = x_501;
goto block_406;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_502; 
x_502 = lean_box(0);
x_407 = x_502;
goto block_430;
}
case 10:
{
lean_object* x_503; 
x_503 = lean_ctor_get(x_2, 1);
lean_inc(x_503);
lean_dec(x_2);
x_2 = x_503;
goto _start;
}
default: 
{
lean_object* x_505; 
x_505 = lean_box(0);
x_5 = x_505;
goto block_406;
}
}
}
case 9:
{
switch (lean_obj_tag(x_2)) {
case 9:
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_3);
x_506 = lean_ctor_get(x_1, 0);
lean_inc(x_506);
lean_dec(x_1);
x_507 = lean_ctor_get(x_2, 0);
lean_inc(x_507);
lean_dec(x_2);
x_508 = l_Lean_Literal_beq(x_506, x_507);
lean_dec(x_507);
lean_dec(x_506);
x_509 = l_Bool_toLBool(x_508);
x_510 = lean_box(x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_4);
return x_511;
}
case 10:
{
lean_object* x_512; 
x_512 = lean_ctor_get(x_2, 1);
lean_inc(x_512);
lean_dec(x_2);
x_2 = x_512;
goto _start;
}
default: 
{
lean_object* x_514; 
x_514 = lean_box(0);
x_5 = x_514;
goto block_406;
}
}
}
case 10:
{
lean_object* x_515; 
x_515 = lean_ctor_get(x_1, 1);
lean_inc(x_515);
lean_dec(x_1);
x_1 = x_515;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_517; 
x_517 = lean_ctor_get(x_2, 1);
lean_inc(x_517);
lean_dec(x_2);
x_2 = x_517;
goto _start;
}
else
{
lean_object* x_519; 
x_519 = lean_box(0);
x_5 = x_519;
goto block_406;
}
}
}
block_406:
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = lean_expr_eqv(x_1, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l___private_Init_Lean_Meta_ExprDefEq_36__etaEq(x_1, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_2);
x_8 = l___private_Init_Lean_Meta_ExprDefEq_36__etaEq(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Expr_getAppFn___main(x_1);
x_10 = l_Lean_Expr_getAppFn___main(x_2);
x_11 = l_Lean_Expr_isMVar(x_9);
if (x_11 == 0)
{
uint8_t x_391; 
x_391 = l_Lean_Expr_isMVar(x_10);
if (x_391 == 0)
{
uint8_t x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_392 = 2;
x_393 = lean_box(x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_4);
return x_394;
}
else
{
lean_object* x_395; 
x_395 = lean_box(0);
x_12 = x_395;
goto block_390;
}
}
else
{
lean_object* x_396; 
x_396 = lean_box(0);
x_12 = x_396;
goto block_390;
}
block_390:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
lean_inc(x_9);
x_13 = l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned(x_9, x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_362; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_10);
x_17 = l___private_Init_Lean_Meta_ExprDefEq_33__isAssigned(x_10, x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_362 = lean_unbox(x_18);
lean_dec(x_18);
if (x_362 == 0)
{
lean_object* x_363; 
lean_inc(x_9);
x_363 = l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic(x_9, x_3, x_19);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_unbox(x_364);
if (x_365 == 0)
{
lean_object* x_366; uint8_t x_367; 
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_unbox(x_364);
lean_dec(x_364);
x_20 = x_367;
x_21 = x_366;
goto block_361;
}
else
{
lean_object* x_368; lean_object* x_369; 
lean_dec(x_364);
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
lean_dec(x_363);
lean_inc(x_3);
lean_inc(x_9);
x_369 = l_Lean_Meta_synthPending(x_9, x_3, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_unbox(x_370);
lean_dec(x_370);
x_20 = x_372;
x_21 = x_371;
goto block_361;
}
else
{
uint8_t x_373; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_373 = !lean_is_exclusive(x_369);
if (x_373 == 0)
{
return x_369;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_369, 0);
x_375 = lean_ctor_get(x_369, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_369);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_363);
if (x_377 == 0)
{
return x_363;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_363, 0);
x_379 = lean_ctor_get(x_363, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_363);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_10);
lean_dec(x_9);
x_381 = l_Lean_Meta_instantiateMVars(x_2, x_3, x_19);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_2 = x_382;
x_4 = x_383;
goto _start;
}
block_361:
{
uint8_t x_22; lean_object* x_23; 
if (x_20 == 0)
{
lean_object* x_339; 
lean_inc(x_10);
x_339 = l___private_Init_Lean_Meta_ExprDefEq_34__isSynthetic(x_10, x_3, x_21);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_unbox(x_340);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_unbox(x_340);
lean_dec(x_340);
x_22 = x_343;
x_23 = x_342;
goto block_338;
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_340);
x_344 = lean_ctor_get(x_339, 1);
lean_inc(x_344);
lean_dec(x_339);
lean_inc(x_3);
lean_inc(x_10);
x_345 = l_Lean_Meta_synthPending(x_10, x_3, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_unbox(x_346);
lean_dec(x_346);
x_22 = x_348;
x_23 = x_347;
goto block_338;
}
else
{
uint8_t x_349; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_345);
if (x_349 == 0)
{
return x_345;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_345, 0);
x_351 = lean_ctor_get(x_345, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_345);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = !lean_is_exclusive(x_339);
if (x_353 == 0)
{
return x_339;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_339, 0);
x_355 = lean_ctor_get(x_339, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_339);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_10);
lean_dec(x_9);
x_357 = l_Lean_Meta_instantiateMVars(x_1, x_3, x_21);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_1 = x_358;
x_4 = x_359;
goto _start;
}
block_338:
{
if (x_22 == 0)
{
lean_object* x_24; 
lean_inc(x_9);
x_24 = l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable(x_9, x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_10);
x_27 = l___private_Init_Lean_Meta_ExprDefEq_35__isAssignable(x_10, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = lean_unbox(x_25);
lean_dec(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
if (x_11 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 0);
lean_dec(x_33);
x_34 = l_Lean_Expr_isMVar(x_10);
lean_dec(x_10);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = 2;
x_36 = lean_box(x_35);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1 + 3);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_27, 0, x_40);
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_45);
return x_27;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec(x_27);
x_47 = l_Lean_Expr_isMVar(x_10);
lean_dec(x_10);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = 2;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 3);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_dec(x_3);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_2);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
return x_61;
}
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_10);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 3);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_27);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_27, 0);
lean_dec(x_65);
x_66 = 0;
x_67 = lean_box(x_66);
lean_ctor_set(x_27, 0, x_67);
return x_27;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_27, 1);
lean_inc(x_68);
lean_dec(x_27);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_27, 1);
x_74 = lean_ctor_get(x_27, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_79);
return x_27;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_dec(x_27);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 1);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_2);
lean_ctor_set(x_85, 2, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
x_87 = lean_ctor_get(x_27, 1);
lean_inc(x_87);
lean_dec(x_27);
x_88 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_87);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
x_92 = l_Bool_toLBool(x_91);
x_93 = lean_box(x_92);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_88, 0);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_88);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_97 = l_Bool_toLBool(x_96);
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
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
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_27, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_9);
x_106 = lean_ctor_get(x_27, 1);
lean_inc(x_106);
lean_dec(x_27);
x_107 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_106);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
x_111 = l_Bool_toLBool(x_110);
x_112 = lean_box(x_111);
lean_ctor_set(x_107, 0, x_112);
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_116 = l_Bool_toLBool(x_115);
x_117 = lean_box(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
return x_118;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_107);
if (x_119 == 0)
{
return x_107;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_107, 0);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_107);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_27, 1);
lean_inc(x_123);
lean_dec(x_27);
x_124 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
x_125 = l_Lean_Meta_getMVarDecl(x_124, x_3, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_129 = l_Lean_Meta_getMVarDecl(x_128, x_3, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
lean_inc(x_133);
lean_inc(x_132);
x_134 = l_Lean_LocalContext_isSubPrefixOf(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_133);
lean_dec(x_132);
x_135 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_131);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
x_139 = l_Bool_toLBool(x_138);
x_140 = lean_box(x_139);
lean_ctor_set(x_135, 0, x_140);
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_135, 0);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_135);
x_143 = lean_unbox(x_141);
lean_dec(x_141);
x_144 = l_Bool_toLBool(x_143);
x_145 = lean_box(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_135);
if (x_147 == 0)
{
return x_135;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_135, 0);
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_135);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; uint8_t x_152; 
x_151 = l_Lean_Expr_isApp(x_1);
if (x_151 == 0)
{
uint8_t x_301; 
x_301 = l_Lean_Expr_isApp(x_2);
if (x_301 == 0)
{
x_152 = x_301;
goto block_300;
}
else
{
lean_object* x_302; 
lean_dec(x_133);
lean_dec(x_132);
x_302 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_302) == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; uint8_t x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_302, 0);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
x_306 = l_Bool_toLBool(x_305);
x_307 = lean_box(x_306);
lean_ctor_set(x_302, 0, x_307);
return x_302;
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_ctor_get(x_302, 0);
x_309 = lean_ctor_get(x_302, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_302);
x_310 = lean_unbox(x_308);
lean_dec(x_308);
x_311 = l_Bool_toLBool(x_310);
x_312 = lean_box(x_311);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_309);
return x_313;
}
}
else
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_302);
if (x_314 == 0)
{
return x_302;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_302, 0);
x_316 = lean_ctor_get(x_302, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_302);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
else
{
x_152 = x_22;
goto block_300;
}
block_300:
{
uint8_t x_153; 
x_153 = l_Lean_Expr_isApp(x_2);
if (x_153 == 0)
{
if (x_151 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
if (x_152 == 0)
{
lean_object* x_154; 
x_154 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
x_158 = l_Bool_toLBool(x_157);
x_159 = lean_box(x_158);
lean_ctor_set(x_154, 0, x_159);
return x_154;
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_154, 0);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_154);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_163 = l_Bool_toLBool(x_162);
x_164 = lean_box(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
return x_165;
}
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_154);
if (x_166 == 0)
{
return x_154;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_154, 0);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_154);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; 
x_170 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_131);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; uint8_t x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
x_174 = l_Bool_toLBool(x_173);
x_175 = lean_box(x_174);
lean_ctor_set(x_170, 0, x_175);
return x_170;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_170, 0);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_170);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_179 = l_Bool_toLBool(x_178);
x_180 = lean_box(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
}
else
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_170);
if (x_182 == 0)
{
return x_170;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_170, 0);
x_184 = lean_ctor_get(x_170, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_170);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
x_186 = l_Lean_LocalContext_isSubPrefixOf(x_133, x_132);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
x_191 = l_Bool_toLBool(x_190);
x_192 = lean_box(x_191);
lean_ctor_set(x_187, 0, x_192);
return x_187;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; 
x_193 = lean_ctor_get(x_187, 0);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_187);
x_195 = lean_unbox(x_193);
lean_dec(x_193);
x_196 = l_Bool_toLBool(x_195);
x_197 = lean_box(x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_194);
return x_198;
}
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_187);
if (x_199 == 0)
{
return x_187;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_187, 0);
x_201 = lean_ctor_get(x_187, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_187);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; 
x_203 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_131);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
x_207 = l_Bool_toLBool(x_206);
x_208 = lean_box(x_207);
lean_ctor_set(x_203, 0, x_208);
return x_203;
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_203, 0);
x_210 = lean_ctor_get(x_203, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_203);
x_211 = lean_unbox(x_209);
lean_dec(x_209);
x_212 = l_Bool_toLBool(x_211);
x_213 = lean_box(x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_210);
return x_214;
}
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_203);
if (x_215 == 0)
{
return x_203;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_203, 0);
x_217 = lean_ctor_get(x_203, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_203);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
}
else
{
if (x_152 == 0)
{
lean_object* x_219; 
lean_dec(x_133);
lean_dec(x_132);
x_219 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
x_223 = l_Bool_toLBool(x_222);
x_224 = lean_box(x_223);
lean_ctor_set(x_219, 0, x_224);
return x_219;
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_219, 0);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_219);
x_227 = lean_unbox(x_225);
lean_dec(x_225);
x_228 = l_Bool_toLBool(x_227);
x_229 = lean_box(x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_226);
return x_230;
}
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_219);
if (x_231 == 0)
{
return x_219;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_219, 0);
x_233 = lean_ctor_get(x_219, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_219);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
if (x_151 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
if (x_152 == 0)
{
lean_object* x_235; 
x_235 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; uint8_t x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = lean_unbox(x_237);
lean_dec(x_237);
x_239 = l_Bool_toLBool(x_238);
x_240 = lean_box(x_239);
lean_ctor_set(x_235, 0, x_240);
return x_235;
}
else
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_235, 0);
x_242 = lean_ctor_get(x_235, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_235);
x_243 = lean_unbox(x_241);
lean_dec(x_241);
x_244 = l_Bool_toLBool(x_243);
x_245 = lean_box(x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_242);
return x_246;
}
}
else
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_235);
if (x_247 == 0)
{
return x_235;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_235, 0);
x_249 = lean_ctor_get(x_235, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_235);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; 
x_251 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_131);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; uint8_t x_254; uint8_t x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_unbox(x_253);
lean_dec(x_253);
x_255 = l_Bool_toLBool(x_254);
x_256 = lean_box(x_255);
lean_ctor_set(x_251, 0, x_256);
return x_251;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_257 = lean_ctor_get(x_251, 0);
x_258 = lean_ctor_get(x_251, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_251);
x_259 = lean_unbox(x_257);
lean_dec(x_257);
x_260 = l_Bool_toLBool(x_259);
x_261 = lean_box(x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_258);
return x_262;
}
}
else
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_251);
if (x_263 == 0)
{
return x_251;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_251, 0);
x_265 = lean_ctor_get(x_251, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_251);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
else
{
uint8_t x_267; 
x_267 = l_Lean_LocalContext_isSubPrefixOf(x_133, x_132);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_1, x_2, x_3, x_131);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_unbox(x_270);
lean_dec(x_270);
x_272 = l_Bool_toLBool(x_271);
x_273 = lean_box(x_272);
lean_ctor_set(x_268, 0, x_273);
return x_268;
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; 
x_274 = lean_ctor_get(x_268, 0);
x_275 = lean_ctor_get(x_268, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_268);
x_276 = lean_unbox(x_274);
lean_dec(x_274);
x_277 = l_Bool_toLBool(x_276);
x_278 = lean_box(x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_268);
if (x_280 == 0)
{
return x_268;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_268, 0);
x_282 = lean_ctor_get(x_268, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_268);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
lean_object* x_284; 
x_284 = l___private_Init_Lean_Meta_ExprDefEq_18__processAssignment(x_2, x_1, x_3, x_131);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; uint8_t x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
x_288 = l_Bool_toLBool(x_287);
x_289 = lean_box(x_288);
lean_ctor_set(x_284, 0, x_289);
return x_284;
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_284, 0);
x_291 = lean_ctor_get(x_284, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_284);
x_292 = lean_unbox(x_290);
lean_dec(x_290);
x_293 = l_Bool_toLBool(x_292);
x_294 = lean_box(x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_291);
return x_295;
}
}
else
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_284);
if (x_296 == 0)
{
return x_284;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_284, 0);
x_298 = lean_ctor_get(x_284, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_284);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_318; 
lean_dec(x_126);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = !lean_is_exclusive(x_129);
if (x_318 == 0)
{
return x_129;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_129, 0);
x_320 = lean_ctor_get(x_129, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_129);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_125);
if (x_322 == 0)
{
return x_125;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_125, 0);
x_324 = lean_ctor_get(x_125, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_125);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_27);
if (x_326 == 0)
{
return x_27;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_27, 0);
x_328 = lean_ctor_get(x_27, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_27);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_24);
if (x_330 == 0)
{
return x_24;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_24, 0);
x_332 = lean_ctor_get(x_24, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_24);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_10);
lean_dec(x_9);
x_334 = l_Lean_Meta_instantiateMVars(x_2, x_3, x_23);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_2 = x_335;
x_4 = x_336;
goto _start;
}
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_10);
lean_dec(x_9);
x_385 = lean_ctor_get(x_13, 1);
lean_inc(x_385);
lean_dec(x_13);
x_386 = l_Lean_Meta_instantiateMVars(x_1, x_3, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_1 = x_387;
x_4 = x_388;
goto _start;
}
}
}
else
{
uint8_t x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = 1;
x_398 = lean_box(x_397);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_4);
return x_399;
}
}
else
{
uint8_t x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = 1;
x_401 = lean_box(x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_4);
return x_402;
}
}
else
{
uint8_t x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_403 = 1;
x_404 = lean_box(x_403);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_4);
return x_405;
}
}
block_430:
{
uint8_t x_408; 
lean_dec(x_407);
x_408 = lean_expr_eqv(x_1, x_2);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_3, 1);
lean_inc(x_409);
x_410 = l_Array_empty___closed__1;
x_411 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_409, x_410, x_1, x_2, x_410, x_3, x_4);
lean_dec(x_2);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; uint8_t x_414; uint8_t x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_411, 0);
x_414 = lean_unbox(x_413);
lean_dec(x_413);
x_415 = l_Bool_toLBool(x_414);
x_416 = lean_box(x_415);
lean_ctor_set(x_411, 0, x_416);
return x_411;
}
else
{
lean_object* x_417; lean_object* x_418; uint8_t x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; 
x_417 = lean_ctor_get(x_411, 0);
x_418 = lean_ctor_get(x_411, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_411);
x_419 = lean_unbox(x_417);
lean_dec(x_417);
x_420 = l_Bool_toLBool(x_419);
x_421 = lean_box(x_420);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_418);
return x_422;
}
}
else
{
uint8_t x_423; 
x_423 = !lean_is_exclusive(x_411);
if (x_423 == 0)
{
return x_411;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_411, 0);
x_425 = lean_ctor_get(x_411, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_411);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
else
{
uint8_t x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_427 = 1;
x_428 = lean_box(x_427);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_4);
return x_429;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_39__isDefEqProofIrrel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_6);
x_8 = l_Lean_Meta_isProp(x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 2;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 2;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_3);
x_20 = l_Lean_Meta_inferType(x_2, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_isExprDefEqAux(x_6, x_21, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = l_Bool_toLBool(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_32 = l_Bool_toLBool(x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_5);
if (x_47 == 0)
{
return x_5;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Meta_tryL(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
switch (x_7) {
case 0:
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_apply_2(x_2, x_3, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_40__isDefEqWHNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_expr_eqv(x_1, x_7);
lean_dec(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_7);
x_13 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_7, x_10, x_4, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
switch (x_15) {
case 0:
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_apply_4(x_3, x_7, x_10, x_4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
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
x_38 = lean_expr_eqv(x_2, x_10);
lean_dec(x_2);
if (x_38 == 0)
{
lean_object* x_39; 
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_7);
x_39 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_7, x_10, x_4, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
switch (x_41) {
case 0:
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = 0;
x_45 = lean_box(x_44);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
case 1:
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
lean_dec(x_51);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_39, 0, x_53);
return x_39;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_dec(x_39);
x_55 = 1;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_apply_4(x_3, x_7, x_10, x_4, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
return x_39;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_39, 0);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_apply_4(x_3, x_7, x_10, x_4, x_11);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
return x_6;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_6);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConst___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
x_7 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1;
x_8 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2;
lean_inc(x_1);
x_9 = l_Lean_WHNF_getStuckMVar___main___rarg(x_6, x_7, x_8, x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_2(x_3, x_4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_4);
x_16 = l_Lean_Meta_synthPending(x_15, x_4, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_apply_2(x_3, x_4, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_apply_3(x_2, x_23, x_4, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_21; lean_object* x_22; 
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_22 = lean_box(x_21);
switch (lean_obj_tag(x_22)) {
case 2:
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(5u);
x_6 = x_23;
goto block_20;
}
case 3:
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(4u);
x_6 = x_24;
goto block_20;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
block_20:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_3, x_6);
lean_inc(x_4);
x_12 = l_Lean_Meta_whnf(x_11, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(x_13, x_4, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
lean_object* l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_RecursorVal_getMajorIdx(x_1);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_7);
lean_dec(x_7);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnf(x_12, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(x_14, x_4, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
lean_object* l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 5:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Expr_getAppFn___main(x_6);
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 2:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = 1;
x_13 = l_Lean_Meta_getConstAux(x_10, x_12, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
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
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
switch (lean_obj_tag(x_21)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_24);
x_26 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_27, x_29);
x_31 = l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3(x_23, x_11, x_30, x_2, x_22);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_23);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_34);
x_36 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_35);
x_37 = lean_mk_array(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_37, x_39);
x_41 = l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4(x_33, x_11, x_40, x_2, x_32);
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_33);
return x_41;
}
default: 
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_13, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
case 10:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_1 = x_54;
goto _start;
}
case 11:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_2);
x_57 = l_Lean_Meta_whnf(x_56, x_2, x_3);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_1 = x_58;
x_3 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_3);
x_17 = l_Lean_Meta_synthPending(x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = l_Lean_Meta_instantiateMVars(x_2, x_3, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_isExprDefEqAux(x_1, x_30, x_3, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_WHNF_getStuckMVar___main___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__2(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__1(x_1, x_2, x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_4);
x_12 = l_Lean_Meta_synthPending(x_11, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__1(x_1, x_2, x_4, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Meta_instantiateMVars(x_3, x_4, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_isExprDefEqAux(x_19, x_2, x_4, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_1, x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_isQuotRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_isRecStuck___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_9);
x_11 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
x_15 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_12, x_14);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_9);
lean_inc(x_16);
x_17 = lean_mk_array(x_16, x_11);
x_18 = lean_nat_sub(x_16, x_13);
lean_dec(x_16);
x_19 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_17, x_18);
x_20 = l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(x_3, x_15, x_19, x_5, x_6);
lean_dec(x_19);
lean_dec(x_15);
return x_20;
}
}
}
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Expr_getAppFn___main(x_2);
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 4, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1___boxed), 6, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 5);
x_13 = l_PersistentArray_empty___closed__3;
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_5, 5, x_13);
lean_inc(x_4);
x_22 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_10, x_11, x_12, x_4, x_25);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_4, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_10, x_11, x_12, x_4, x_35);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_32, 0);
lean_dec(x_42);
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec(x_32);
x_14 = x_45;
x_15 = x_46;
goto block_21;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_dec(x_22);
x_14 = x_47;
x_15 = x_48;
goto block_21;
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_10, x_11, x_12, x_4, x_15);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_64; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_5, 1);
x_51 = lean_ctor_get(x_5, 2);
x_52 = lean_ctor_get(x_5, 3);
x_53 = lean_ctor_get(x_5, 4);
x_54 = lean_ctor_get(x_5, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_5);
x_55 = l_PersistentArray_empty___closed__3;
lean_inc(x_50);
lean_inc(x_49);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
lean_ctor_set(x_56, 5, x_55);
lean_inc(x_4);
x_64 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_7, x_8, x_4, x_56);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_49, x_50, x_54, x_4, x_67);
lean_dec(x_4);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = l___private_Init_Lean_Meta_LevelDefEq_11__processPostponed(x_4, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_49, x_50, x_54, x_4, x_76);
lean_dec(x_4);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_4);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
lean_dec(x_73);
x_57 = x_84;
x_58 = x_85;
goto block_63;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
lean_dec(x_64);
x_57 = x_86;
x_58 = x_87;
goto block_63;
}
block_63:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l___private_Init_Lean_Meta_LevelDefEq_12__restore(x_49, x_50, x_54, x_4, x_58);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_40__isDefEqWHNF___at_Lean_Meta_isExprDefEqAuxImpl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
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
x_12 = lean_expr_eqv(x_1, x_6);
lean_dec(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_13 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_6, x_9, x_3, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
switch (x_15) {
case 0:
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_59; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_33 = x_13;
} else {
 lean_dec_ref(x_13);
 x_33 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_59 = l_Lean_Meta_isDefEqOffset(x_6, x_9, x_3, x_32);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
switch (x_61) {
case 0:
{
uint8_t x_62; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
lean_dec(x_63);
x_64 = 0;
x_65 = lean_box(x_64);
lean_ctor_set(x_59, 0, x_65);
return x_59;
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
case 1:
{
uint8_t x_70; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_59);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_59, 0);
lean_dec(x_71);
x_72 = 1;
x_73 = lean_box(x_72);
lean_ctor_set(x_59, 0, x_73);
return x_59;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
default: 
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_dec(x_59);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_79 = l___private_Init_Lean_Meta_ExprDefEq_32__isDefEqDelta(x_6, x_9, x_3, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
switch (x_81) {
case 0:
{
uint8_t x_82; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_79, 0, x_85);
return x_79;
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
case 1:
{
uint8_t x_90; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
lean_dec(x_91);
x_92 = 1;
x_93 = lean_box(x_92);
lean_ctor_set(x_79, 0, x_93);
return x_79;
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
lean_dec(x_79);
x_95 = 1;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
default: 
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_dec(x_79);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_99 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_6, x_9, x_3, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_9);
x_103 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_9, x_6, x_3, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unbox(x_104);
lean_dec(x_104);
x_34 = x_106;
x_35 = x_105;
goto block_58;
}
else
{
uint8_t x_107; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
return x_103;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_103);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_unbox(x_100);
lean_dec(x_100);
x_34 = x_112;
x_35 = x_111;
goto block_58;
}
}
else
{
uint8_t x_113; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_99);
if (x_113 == 0)
{
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_99, 0);
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_99);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_79);
if (x_117 == 0)
{
return x_79;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_79, 0);
x_119 = lean_ctor_get(x_79, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_79);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_59);
if (x_121 == 0)
{
return x_59;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_59, 0);
x_123 = lean_ctor_get(x_59, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_59);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
block_58:
{
if (x_34 == 0)
{
lean_dec(x_33);
switch (lean_obj_tag(x_6)) {
case 4:
{
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = l_Lean_Meta_isListLevelDefEqAux___main(x_36, x_37, x_3, x_35);
lean_dec(x_3);
return x_38;
}
else
{
lean_object* x_39; 
lean_inc(x_6);
x_39 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_35);
return x_39;
}
}
case 5:
{
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Expr_getAppFn___main(x_6);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_41 = l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1(x_6, x_9, x_40, x_3, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_6);
x_45 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
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
lean_inc(x_6);
x_54 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_35);
return x_54;
}
}
default: 
{
lean_object* x_55; 
lean_inc(x_6);
x_55 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_35);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_56 = lean_box(x_34);
if (lean_is_scalar(x_33)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_33;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_35);
return x_57;
}
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_13);
if (x_125 == 0)
{
return x_13;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_13, 0);
x_127 = lean_ctor_get(x_13, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_13);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
x_129 = lean_expr_eqv(x_2, x_9);
lean_dec(x_2);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_130 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_6, x_9, x_3, x_10);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
switch (x_132) {
case 0:
{
uint8_t x_133; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_130);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_130, 0);
lean_dec(x_134);
x_135 = 0;
x_136 = lean_box(x_135);
lean_ctor_set(x_130, 0, x_136);
return x_130;
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
lean_dec(x_130);
x_138 = 0;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
case 1:
{
uint8_t x_141; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_130);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_130, 0);
lean_dec(x_142);
x_143 = 1;
x_144 = lean_box(x_143);
lean_ctor_set(x_130, 0, x_144);
return x_130;
}
else
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_130, 1);
lean_inc(x_145);
lean_dec(x_130);
x_146 = 1;
x_147 = lean_box(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
default: 
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_176; 
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_150 = x_130;
} else {
 lean_dec_ref(x_130);
 x_150 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_176 = l_Lean_Meta_isDefEqOffset(x_6, x_9, x_3, x_149);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
switch (x_178) {
case 0:
{
uint8_t x_179; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 0);
lean_dec(x_180);
x_181 = 0;
x_182 = lean_box(x_181);
lean_ctor_set(x_176, 0, x_182);
return x_176;
}
else
{
lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
lean_dec(x_176);
x_184 = 0;
x_185 = lean_box(x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
}
case 1:
{
uint8_t x_187; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_187 = !lean_is_exclusive(x_176);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_176, 0);
lean_dec(x_188);
x_189 = 1;
x_190 = lean_box(x_189);
lean_ctor_set(x_176, 0, x_190);
return x_176;
}
else
{
lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_dec(x_176);
x_192 = 1;
x_193 = lean_box(x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
}
default: 
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_176, 1);
lean_inc(x_195);
lean_dec(x_176);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_196 = l___private_Init_Lean_Meta_ExprDefEq_32__isDefEqDelta(x_6, x_9, x_3, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
switch (x_198) {
case 0:
{
uint8_t x_199; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_196);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_196, 0);
lean_dec(x_200);
x_201 = 0;
x_202 = lean_box(x_201);
lean_ctor_set(x_196, 0, x_202);
return x_196;
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
lean_dec(x_196);
x_204 = 0;
x_205 = lean_box(x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
}
case 1:
{
uint8_t x_207; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_207 = !lean_is_exclusive(x_196);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_196, 0);
lean_dec(x_208);
x_209 = 1;
x_210 = lean_box(x_209);
lean_ctor_set(x_196, 0, x_210);
return x_196;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
lean_dec(x_196);
x_212 = 1;
x_213 = lean_box(x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
}
default: 
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_196, 1);
lean_inc(x_215);
lean_dec(x_196);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_216 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_6, x_9, x_3, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_217);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_9);
x_220 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_9, x_6, x_3, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_unbox(x_221);
lean_dec(x_221);
x_151 = x_223;
x_152 = x_222;
goto block_175;
}
else
{
uint8_t x_224; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
return x_220;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_220);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_228);
lean_dec(x_216);
x_229 = lean_unbox(x_217);
lean_dec(x_217);
x_151 = x_229;
x_152 = x_228;
goto block_175;
}
}
else
{
uint8_t x_230; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_230 = !lean_is_exclusive(x_216);
if (x_230 == 0)
{
return x_216;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_216, 0);
x_232 = lean_ctor_get(x_216, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_216);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_196);
if (x_234 == 0)
{
return x_196;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_196, 0);
x_236 = lean_ctor_get(x_196, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_196);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_176);
if (x_238 == 0)
{
return x_176;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_176, 0);
x_240 = lean_ctor_get(x_176, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
block_175:
{
if (x_151 == 0)
{
lean_dec(x_150);
switch (lean_obj_tag(x_6)) {
case 4:
{
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_6, 1);
lean_inc(x_153);
lean_dec(x_6);
x_154 = lean_ctor_get(x_9, 1);
lean_inc(x_154);
lean_dec(x_9);
x_155 = l_Lean_Meta_isListLevelDefEqAux___main(x_153, x_154, x_3, x_152);
lean_dec(x_3);
return x_155;
}
else
{
lean_object* x_156; 
lean_inc(x_6);
x_156 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_152);
return x_156;
}
}
case 5:
{
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_157; lean_object* x_158; 
x_157 = l_Lean_Expr_getAppFn___main(x_6);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_158 = l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1(x_6, x_9, x_157, x_3, x_152);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unbox(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_159);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
lean_inc(x_6);
x_162 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_161);
return x_162;
}
else
{
uint8_t x_163; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_158);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_158, 0);
lean_dec(x_164);
return x_158;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
lean_dec(x_158);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_167 = !lean_is_exclusive(x_158);
if (x_167 == 0)
{
return x_158;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_158, 0);
x_169 = lean_ctor_get(x_158, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_158);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; 
lean_inc(x_6);
x_171 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_152);
return x_171;
}
}
default: 
{
lean_object* x_172; 
lean_inc(x_6);
x_172 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_152);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_173 = lean_box(x_151);
if (lean_is_scalar(x_150)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_150;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_152);
return x_174;
}
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_242 = !lean_is_exclusive(x_130);
if (x_242 == 0)
{
return x_130;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_130, 0);
x_244 = lean_ctor_get(x_130, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_130);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
uint8_t x_246; lean_object* x_247; lean_object* x_271; 
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_271 = l_Lean_Meta_isDefEqOffset(x_6, x_9, x_3, x_10);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_unbox(x_272);
lean_dec(x_272);
switch (x_273) {
case 0:
{
uint8_t x_274; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_274 = !lean_is_exclusive(x_271);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_271, 0);
lean_dec(x_275);
x_276 = 0;
x_277 = lean_box(x_276);
lean_ctor_set(x_271, 0, x_277);
return x_271;
}
else
{
lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_271, 1);
lean_inc(x_278);
lean_dec(x_271);
x_279 = 0;
x_280 = lean_box(x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_278);
return x_281;
}
}
case 1:
{
uint8_t x_282; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_282 = !lean_is_exclusive(x_271);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_271, 0);
lean_dec(x_283);
x_284 = 1;
x_285 = lean_box(x_284);
lean_ctor_set(x_271, 0, x_285);
return x_271;
}
else
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_271, 1);
lean_inc(x_286);
lean_dec(x_271);
x_287 = 1;
x_288 = lean_box(x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
default: 
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_271, 1);
lean_inc(x_290);
lean_dec(x_271);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_291 = l___private_Init_Lean_Meta_ExprDefEq_32__isDefEqDelta(x_6, x_9, x_3, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
switch (x_293) {
case 0:
{
uint8_t x_294; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_294 = !lean_is_exclusive(x_291);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_291, 0);
lean_dec(x_295);
x_296 = 0;
x_297 = lean_box(x_296);
lean_ctor_set(x_291, 0, x_297);
return x_291;
}
else
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; 
x_298 = lean_ctor_get(x_291, 1);
lean_inc(x_298);
lean_dec(x_291);
x_299 = 0;
x_300 = lean_box(x_299);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
return x_301;
}
}
case 1:
{
uint8_t x_302; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_302 = !lean_is_exclusive(x_291);
if (x_302 == 0)
{
lean_object* x_303; uint8_t x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_291, 0);
lean_dec(x_303);
x_304 = 1;
x_305 = lean_box(x_304);
lean_ctor_set(x_291, 0, x_305);
return x_291;
}
else
{
lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_291, 1);
lean_inc(x_306);
lean_dec(x_291);
x_307 = 1;
x_308 = lean_box(x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
return x_309;
}
}
default: 
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_291, 1);
lean_inc(x_310);
lean_dec(x_291);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_311 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_6, x_9, x_3, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_unbox(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_312);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_9);
x_315 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(x_9, x_6, x_3, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_unbox(x_316);
lean_dec(x_316);
x_246 = x_318;
x_247 = x_317;
goto block_270;
}
else
{
uint8_t x_319; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_319 = !lean_is_exclusive(x_315);
if (x_319 == 0)
{
return x_315;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_315, 0);
x_321 = lean_ctor_get(x_315, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_315);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_311, 1);
lean_inc(x_323);
lean_dec(x_311);
x_324 = lean_unbox(x_312);
lean_dec(x_312);
x_246 = x_324;
x_247 = x_323;
goto block_270;
}
}
else
{
uint8_t x_325; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_325 = !lean_is_exclusive(x_311);
if (x_325 == 0)
{
return x_311;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_311, 0);
x_327 = lean_ctor_get(x_311, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_311);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_329 = !lean_is_exclusive(x_291);
if (x_329 == 0)
{
return x_291;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_291, 0);
x_331 = lean_ctor_get(x_291, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_291);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_333 = !lean_is_exclusive(x_271);
if (x_333 == 0)
{
return x_271;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_271, 0);
x_335 = lean_ctor_get(x_271, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_271);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
block_270:
{
if (x_246 == 0)
{
lean_dec(x_11);
switch (lean_obj_tag(x_6)) {
case 4:
{
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_6, 1);
lean_inc(x_248);
lean_dec(x_6);
x_249 = lean_ctor_get(x_9, 1);
lean_inc(x_249);
lean_dec(x_9);
x_250 = l_Lean_Meta_isListLevelDefEqAux___main(x_248, x_249, x_3, x_247);
lean_dec(x_3);
return x_250;
}
else
{
lean_object* x_251; 
lean_inc(x_6);
x_251 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_247);
return x_251;
}
}
case 5:
{
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lean_Expr_getAppFn___main(x_6);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_6);
x_253 = l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1(x_6, x_9, x_252, x_3, x_247);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_unbox(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_254);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
lean_inc(x_6);
x_257 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_256);
return x_257;
}
else
{
uint8_t x_258; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_258 = !lean_is_exclusive(x_253);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_253, 0);
lean_dec(x_259);
return x_253;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_253, 1);
lean_inc(x_260);
lean_dec(x_253);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_262 = !lean_is_exclusive(x_253);
if (x_262 == 0)
{
return x_253;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_253, 0);
x_264 = lean_ctor_get(x_253, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_253);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_object* x_266; 
lean_inc(x_6);
x_266 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_247);
return x_266;
}
}
default: 
{
lean_object* x_267; 
lean_inc(x_6);
x_267 = l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___at___private_Init_Lean_Meta_ExprDefEq_42__isDefEqOnFailure___spec__5(x_6, x_9, x_6, x_3, x_247);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_268 = lean_box(x_246);
if (lean_is_scalar(x_11)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_11;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_247);
return x_269;
}
}
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_8);
if (x_337 == 0)
{
return x_8;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_8, 0);
x_339 = lean_ctor_get(x_8, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_8);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = !lean_is_exclusive(x_5);
if (x_341 == 0)
{
return x_5;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_5, 0);
x_343 = lean_ctor_get(x_5, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_5);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
}
lean_object* _init_l_Lean_Meta_isExprDefEqAuxImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_isExprDefEqAuxImpl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l_Lean_Meta_isExprDefEqAuxImpl___closed__1;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isExprDefEqAuxImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_4, 4);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
lean_dec(x_56);
if (x_57 == 0)
{
x_5 = x_4;
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = l_Lean_Meta_isExprDefEqAuxImpl___closed__2;
x_59 = l___private_Init_Lean_Trace_5__checkTraceOption___at_Lean_Meta_check___spec__3(x_58, x_3, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_5 = x_62;
goto block_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
lean_inc(x_1);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_1);
x_65 = l_Lean_Meta_Exception_toMessageData___closed__51;
x_66 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_2);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_2);
x_68 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_isExprDefEqAuxImpl___closed__1;
x_70 = l___private_Init_Lean_Trace_3__addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_69, x_68, x_3, x_63);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_5 = x_71;
goto block_55;
}
}
block_55:
{
lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Init_Lean_Meta_ExprDefEq_38__isDefEqQuick___main(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
switch (x_8) {
case 0:
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
case 1:
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l___private_Init_Lean_Meta_ExprDefEq_39__isDefEqProofIrrel(x_1, x_2, x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
switch (x_28) {
case 0:
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
case 1:
{
uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 0);
lean_dec(x_38);
x_39 = 1;
x_40 = lean_box(x_39);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
default: 
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_dec(x_26);
x_46 = l___private_Init_Lean_Meta_ExprDefEq_40__isDefEqWHNF___at_Lean_Meta_isExprDefEqAuxImpl___spec__2(x_1, x_2, x_3, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
return x_6;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
lean_object* l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_try___at_Lean_Meta_isExprDefEqAuxImpl___spec__1___lambda__1(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_setIsExprDefEqAuxRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAuxImpl), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setIsExprDefEqAuxRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_isExprDefEqAuxRef;
x_3 = l_Lean_Meta_setIsExprDefEqAuxRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Lean_ProjFns(lean_object*);
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_Check(lean_object*);
lean_object* initialize_Init_Lean_Meta_Offset(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Offset(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1 = _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3);
l_Lean_Meta_CheckAssignment_Lean_MonadCache = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache);
l_Lean_Meta_CheckAssignment_check___main___closed__1 = _init_l_Lean_Meta_CheckAssignment_check___main___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_check___main___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__4);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__5);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__6);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__7);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__8);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__9);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__10);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__11);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__12);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__13);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__14);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__15);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__16);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__17);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__18);
l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19 = _init_l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_10__checkAssignmentFailure___closed__19);
l_Lean_Meta_checkAssignment___closed__1 = _init_l_Lean_Meta_checkAssignment___closed__1();
lean_mark_persistent(l_Lean_Meta_checkAssignment___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApprox___main___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__4);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__5);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__6);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__7);
l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8 = _init_l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_17__processAssignmentAux___main___closed__8);
l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__4);
l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5 = _init_l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_21__isDefEqLeft___closed__5);
l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_22__isDefEqRight___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_23__isDefEqLeftRight___closed__3);
l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1 = _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__1);
l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2 = _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__2);
l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3 = _init_l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_try___at___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___spec__1___lambda__2___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_24__tryHeuristic___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_41__unstuckMVar___closed__2);
l_Lean_Meta_isExprDefEqAuxImpl___closed__1 = _init_l_Lean_Meta_isExprDefEqAuxImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_isExprDefEqAuxImpl___closed__1);
l_Lean_Meta_isExprDefEqAuxImpl___closed__2 = _init_l_Lean_Meta_isExprDefEqAuxImpl___closed__2();
lean_mark_persistent(l_Lean_Meta_isExprDefEqAuxImpl___closed__2);
l_Lean_Meta_setIsExprDefEqAuxRef___closed__1 = _init_l_Lean_Meta_setIsExprDefEqAuxRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setIsExprDefEqAuxRef___closed__1);
res = l_Lean_Meta_setIsExprDefEqAuxRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
