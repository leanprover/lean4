// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___boxed(lean_object**);
static lean_object* l_Lean_MVarId_induction___closed__3;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3;
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_fields___default;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2___boxed(lean_object**);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_localDeclDependsOn___at_Lean_MVarId_clear___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInductionSubgoal;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3484_(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_induction___lambda__2___closed__2;
lean_object* l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_induction___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAltVarNames;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_subst___default;
static lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_MVarId_induction___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedInductionSubgoal___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object**);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_MVarId_induction___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3;
static lean_object* l_Lean_Meta_instInhabitedAltVarNames___closed__1;
static lean_object* l_Lean_MVarId_induction___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object**);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AltVarNames_varNames___default;
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___boxed(lean_object**);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
static lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2;
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4;
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7;
static lean_object* l_Lean_MVarId_induction___closed__1;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_induction___closed__4;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
static lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
lean_object* l_panic___at_Lean_Expr_fvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
static lean_object* l_Lean_MVarId_induction___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_AltVarNames_explicit___default;
LEAN_EXPORT lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1;
extern lean_object* l_Lean_instInhabitedLevel;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
default: 
{
uint8_t x_8; uint8_t x_9; 
x_8 = 0;
x_9 = l_Lean_Expr_isHeadBetaTarget(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Expr_headBeta(x_1);
x_1 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_app___override(x_1, x_5);
x_12 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induction", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed recursor", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to generate type class instance parameter", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_infer_type(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnfForall(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_synthInstance(x_19, x_20, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(x_4, x_1, x_2, x_12, x_22, x_5, x_6, x_7, x_8, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_1, x_27, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(x_4, x_1, x_2, x_12, x_29, x_5, x_6, x_7, x_8, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_38 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_37, x_1, x_38, x_5, x_6, x_7, x_8, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_dec(x_3);
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_array_get_size(x_2);
x_51 = lean_nat_dec_lt(x_49, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_2);
x_52 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_53 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_52, x_1, x_53, x_5, x_6, x_7, x_8, x_9);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_49);
lean_dec(x_49);
x_56 = l_Lean_Expr_app___override(x_4, x_55);
x_3 = x_48;
x_4 = x_56;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_fields___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_fields___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInductionSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInductionSubgoal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedInductionSubgoal___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnfForall(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_expr_instantiate1(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_21 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_21, x_4, x_5, x_6, x_7, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static uint8_t _init_l_Lean_Meta_AltVarNames_explicit___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AltVarNames_varNames___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAltVarNames___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAltVarNames() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedAltVarNames___closed__1;
return x_1;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1;
x_2 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_nat_add(x_12, x_11);
x_14 = lean_nat_sub(x_6, x_13);
lean_dec(x_13);
x_15 = lean_nat_add(x_4, x_11);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_nat_dec_lt(x_14, x_3);
x_18 = lean_nat_sub(x_14, x_4);
x_19 = lean_nat_sub(x_18, x_11);
lean_dec(x_18);
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_19, x_20);
lean_dec(x_20);
if (x_17 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4;
x_23 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_22);
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_24 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_22);
x_25 = l_Lean_Expr_fvar___override(x_24);
x_26 = l_Lean_Meta_FVarSubst_insert(x_8, x_23, x_25);
x_7 = x_12;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_array_fget(x_5, x_19);
lean_dec(x_19);
x_29 = l_Lean_Expr_fvar___override(x_28);
x_30 = l_Lean_Meta_FVarSubst_insert(x_8, x_23, x_29);
x_7 = x_12;
x_8 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; 
x_32 = lean_array_fget(x_1, x_14);
lean_dec(x_14);
if (x_21 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_33 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4;
x_34 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_33);
x_35 = l_Lean_Expr_fvar___override(x_34);
x_36 = l_Lean_Meta_FVarSubst_insert(x_8, x_32, x_35);
x_7 = x_12;
x_8 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_array_fget(x_5, x_19);
lean_dec(x_19);
x_39 = l_Lean_Expr_fvar___override(x_38);
x_40 = l_Lean_Meta_FVarSubst_insert(x_8, x_32, x_39);
x_7 = x_12;
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_dec(x_14);
x_7 = x_12;
goto _start;
}
}
else
{
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_16 = l_Lean_Expr_app___override(x_14, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_15, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_16);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_12);
x_29 = l_Lean_Expr_app___override(x_27, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_28, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
x_5 = x_33;
x_10 = x_32;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_39 = x_30;
} else {
 lean_dec_ref(x_30);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_10);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_20);
x_26 = lean_nat_sub(x_1, x_2);
lean_dec(x_1);
x_27 = lean_array_get_size(x_3);
x_28 = lean_array_get_size(x_4);
x_29 = lean_nat_sub(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_90 = lean_array_get_size(x_13);
x_91 = lean_nat_dec_lt(x_11, x_90);
lean_dec(x_90);
x_92 = l_Lean_Name_append(x_17, x_18);
lean_dec(x_17);
lean_inc(x_21);
x_93 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_92, x_21, x_22, x_23, x_24, x_25);
if (x_91 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Meta_instInhabitedAltVarNames___closed__1;
x_32 = x_96;
x_33 = x_94;
x_34 = x_95;
goto block_89;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_array_fget(x_13, x_11);
x_32 = x_99;
x_33 = x_97;
x_34 = x_98;
goto block_89;
}
block_89:
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_33);
x_35 = l_Lean_Expr_app___override(x_5, x_33);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_6);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_7, x_33, x_21, x_22, x_23, x_24, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_mvarId_x21(x_33);
lean_inc(x_8);
x_40 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_41 = l_Lean_MVarId_tryClear(x_39, x_40, x_21, x_22, x_23, x_24, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_78; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
x_78 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = 1;
x_45 = x_79;
goto block_77;
}
else
{
uint8_t x_80; 
x_80 = 0;
x_45 = x_80;
goto block_77;
}
block_77:
{
uint8_t x_46; lean_object* x_47; 
x_46 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_47 = l_Lean_Meta_introNCore(x_42, x_26, x_44, x_45, x_46, x_21, x_22, x_23, x_24, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = 1;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_54 = l_Lean_Meta_introNCore(x_51, x_31, x_52, x_46, x_53, x_21, x_22, x_23, x_24, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_9);
lean_inc(x_27);
x_59 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_3, x_4, x_27, x_28, x_57, x_27, x_27, x_9);
lean_dec(x_57);
lean_dec(x_28);
lean_dec(x_27);
x_60 = lean_array_get_size(x_50);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_61, x_62, x_50);
x_64 = lean_nat_add(x_10, x_30);
lean_dec(x_10);
x_65 = lean_nat_add(x_11, x_30);
lean_dec(x_11);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_59);
x_67 = lean_array_push(x_12, x_66);
x_68 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_13, x_14, x_3, x_8, x_4, x_9, x_2, x_15, x_64, x_65, x_35, x_37, x_16, x_67, x_21, x_22, x_23, x_24, x_56);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
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
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_47);
if (x_73 == 0)
{
return x_47;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_47, 0);
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_47);
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
uint8_t x_81; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
return x_41;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_41, 0);
x_83 = lean_ctor_get(x_41, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_41);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_36);
if (x_85 == 0)
{
return x_36;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_36, 0);
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_36);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Tactic.Induction", 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Meta.Tactic.Induction.0.Lean.Meta.finalize.loop", 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(115u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_dec(x_17);
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_43; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_26 = l_Lean_Expr_headBeta(x_24);
x_43 = l_Lean_BinderInfo_isInstImplicit(x_25);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_27 = x_44;
goto block_42;
}
else
{
uint8_t x_45; 
x_45 = l_Array_isEmpty___rarg(x_12);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_27 = x_46;
goto block_42;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
x_48 = l_Lean_Meta_synthInstance_x3f(x_26, x_47, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Name_append(x_16, x_23);
lean_dec(x_16);
lean_inc(x_18);
x_52 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_51, x_18, x_19, x_20, x_21, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_53);
x_55 = l_Lean_Expr_app___override(x_5, x_53);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_56 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_53, x_18, x_19, x_20, x_21, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_9, x_59);
lean_dec(x_9);
x_61 = lean_nat_add(x_10, x_59);
lean_dec(x_10);
x_62 = l_Lean_Expr_mvarId_x21(x_53);
x_63 = lean_box(0);
x_64 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_array_push(x_11, x_65);
x_67 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_60, x_61, x_55, x_57, x_15, x_66, x_18, x_19, x_20, x_21, x_58);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_16);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_ctor_get(x_49, 0);
lean_inc(x_73);
lean_dec(x_49);
lean_inc(x_73);
x_74 = l_Lean_Expr_app___override(x_5, x_73);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_75 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_73, x_18, x_19, x_20, x_21, x_72);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_9, x_78);
lean_dec(x_9);
x_80 = lean_nat_add(x_10, x_78);
lean_dec(x_10);
x_81 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_79, x_80, x_74, x_76, x_15, x_11, x_18, x_19, x_20, x_21, x_77);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_48);
if (x_86 == 0)
{
return x_48;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_48, 0);
x_88 = lean_ctor_get(x_48, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_48);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
block_42:
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_27);
lean_inc(x_26);
x_28 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_26);
x_29 = lean_nat_dec_lt(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(x_28, x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_23, x_26, x_30, x_18, x_19, x_20, x_21, x_22);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_6, x_33, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(x_28, x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_23, x_26, x_35, x_18, x_19, x_20, x_21, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
x_91 = l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(x_90, x_18, x_19, x_20, x_21, x_22);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_whnfForall(x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isForall(x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_27 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_28, x_16, x_17, x_18, x_19, x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_35, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_3, 3);
lean_inc(x_37);
x_38 = lean_nat_dec_lt(x_10, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_14 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_40 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_41 = l_Lean_Meta_throwTacticEx___rarg(x_39, x_1, x_40, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_42, x_16, x_17, x_18, x_19, x_43);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_49, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_52 = lean_nat_dec_eq(x_10, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_1);
x_53 = l_Lean_MVarId_getTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_nat_dec_le(x_9, x_11);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_22, x_8, x_4, x_6, x_12, x_1, x_5, x_7, x_10, x_11, x_15, x_2, x_3, x_9, x_14, x_54, x_57, x_16, x_17, x_18, x_19, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_60 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_59, x_1, x_60, x_16, x_17, x_18, x_19, x_55);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_22, x_8, x_4, x_6, x_12, x_1, x_5, x_7, x_10, x_11, x_15, x_2, x_3, x_9, x_14, x_54, x_62, x_16, x_17, x_18, x_19, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_54);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
return x_53;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_53, 0);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_53);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_inc(x_22);
lean_inc(x_12);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_22);
x_74 = lean_array_get_size(x_6);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
lean_inc(x_5);
x_77 = l_Lean_Expr_app___override(x_12, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_78 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_22, x_5, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_10, x_81);
lean_dec(x_10);
x_83 = lean_nat_add(x_82, x_74);
lean_dec(x_74);
lean_dec(x_82);
x_84 = 1;
x_10 = x_83;
x_12 = x_77;
x_13 = x_79;
x_14 = x_84;
x_20 = x_80;
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_74, x_74);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_73);
lean_inc(x_5);
x_91 = l_Lean_Expr_app___override(x_12, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_92 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_22, x_5, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_10, x_95);
lean_dec(x_10);
x_97 = lean_nat_add(x_96, x_74);
lean_dec(x_74);
lean_dec(x_96);
x_98 = 1;
x_10 = x_97;
x_12 = x_91;
x_13 = x_93;
x_14 = x_98;
x_20 = x_94;
goto _start;
}
else
{
uint8_t x_100; 
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
return x_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
lean_dec(x_22);
lean_dec(x_12);
x_104 = 0;
x_105 = lean_usize_of_nat(x_74);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_106 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_6, x_104, x_105, x_73, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
lean_inc(x_5);
x_111 = l_Lean_Expr_app___override(x_109, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_112 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_110, x_5, x_16, x_17, x_18, x_19, x_108);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_10, x_115);
lean_dec(x_10);
x_117 = lean_nat_add(x_116, x_74);
lean_dec(x_74);
lean_dec(x_116);
x_118 = 1;
x_10 = x_117;
x_12 = x_111;
x_13 = x_113;
x_14 = x_118;
x_20 = x_114;
goto _start;
}
else
{
uint8_t x_120; 
lean_dec(x_111);
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
return x_112;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_112, 0);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_112);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_106);
if (x_124 == 0)
{
return x_106;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_106, 0);
x_126 = lean_ctor_get(x_106, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_106);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
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
uint8_t x_128; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_21);
if (x_128 == 0)
{
return x_21;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_21, 0);
x_130 = lean_ctor_get(x_21, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_21);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; lean_object* x_27; 
x_26 = lean_unbox(x_16);
lean_dec(x_16);
x_27 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_unbox(x_15);
lean_dec(x_15);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = lean_infer_type(x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 7);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_List_lengthTRAux___rarg(x_21, x_22);
lean_dec(x_21);
x_24 = lean_ctor_get(x_3, 5);
lean_inc(x_24);
x_25 = l_List_lengthTRAux___rarg(x_24, x_22);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_30 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_23, x_27, x_22, x_8, x_19, x_28, x_29, x_9, x_10, x_11, x_12, x_20);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected major premise type", 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_indentExpr(x_2);
x_9 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_1, x_12, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type is ill-formed", 32);
return x_1;
}
}
static lean_object* _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 1);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_le(x_18, x_17);
lean_dec(x_18);
if (x_19 == 0)
{
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
x_21 = l_Lean_indentExpr(x_3);
x_22 = l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_5 = x_16;
x_10 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_MVarId_induction___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
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
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it depends on index occurring at position #", 79);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 6);
x_18 = l_List_elem___at_Lean_MVarId_induction___spec__2(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isFVar(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_5);
x_24 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_9);
x_25 = l_Lean_FVarId_getDecl(x_24, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_fvarId_x21(x_4);
x_29 = l_Lean_localDeclDependsOn___at_Lean_MVarId_clear___spec__1(x_26, x_28, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_5);
x_40 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
x_46 = l_Nat_repr(x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_51, x_9, x_10, x_11, x_12, x_38);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs in previous arguments", 67);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
lean_dec(x_9);
x_15 = lean_nat_dec_lt(x_2, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_5);
x_18 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_4);
x_19 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_4, x_18, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_10, x_11, x_12, x_13, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_5);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_5);
x_27 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_indentExpr(x_8);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_34, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_36);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs more than once", 60);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = lean_nat_dec_lt(x_21, x_8);
x_23 = lean_nat_dec_eq(x_21, x_6);
if (x_22 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4;
x_67 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_66);
x_24 = x_67;
goto block_65;
}
else
{
lean_object* x_68; 
x_68 = lean_array_fget(x_5, x_21);
x_24 = x_68;
goto block_65;
}
block_65:
{
if (x_23 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_eqv(x_24, x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_27 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(x_6, x_21, x_3, x_24, x_7, x_2, x_1, x_4, x_26, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_10 = x_19;
x_15 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_7);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_7);
x_35 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = l_Lean_indentExpr(x_4);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_2);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_46 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(x_6, x_21, x_3, x_24, x_7, x_2, x_1, x_4, x_44, x_11, x_12, x_13, x_14, x_45);
lean_dec(x_21);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_10 = x_19;
x_15 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
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
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_58 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(x_6, x_21, x_3, x_24, x_7, x_2, x_1, x_4, x_57, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_10 = x_19;
x_15 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_15);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_get_size(x_1);
lean_inc(x_14);
lean_inc(x_7);
x_15 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3(x_2, x_3, x_4, x_5, x_1, x_6, x_7, x_14, x_14, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type index ", 25);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not a variable", 18);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_1, x_2);
x_15 = l_Lean_Expr_isFVar(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_6);
x_21 = l_Lean_indentExpr(x_6);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_4);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_3, x_24, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1(x_1, x_3, x_4, x_5, x_6, x_2, x_14, x_26, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1(x_1, x_3, x_4, x_5, x_6, x_2, x_14, x_33, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_uget(x_8, x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_8, x_7, x_17);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_le(x_19, x_16);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2(x_5, x_16, x_1, x_2, x_3, x_4, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_27 = lean_array_uset(x_18, x_7, x_23);
x_7 = x_26;
x_8 = x_27;
x_13 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_4);
x_33 = l_Lean_indentExpr(x_4);
x_34 = l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2(x_5, x_16, x_1, x_2, x_3, x_4, x_39, x_9, x_10, x_11, x_12, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = lean_usize_add(x_7, x_44);
x_46 = lean_array_uset(x_18, x_7, x_42);
x_7 = x_45;
x_8 = x_46;
x_13 = x_43;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Expr_fvarId_x21(x_7);
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_8, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
if (x_12 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
lean_dec(x_8);
x_15 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4;
x_16 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_15);
x_17 = l_Lean_Expr_fvar___override(x_16);
x_18 = l_Lean_Meta_FVarSubst_insert(x_9, x_10, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_23 = lean_array_fget(x_1, x_8);
lean_dec(x_8);
x_24 = l_Lean_Expr_fvar___override(x_23);
x_25 = l_Lean_Meta_FVarSubst_insert(x_9, x_10, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
x_5 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_instInhabitedLevel;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_box(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
lean_inc(x_3);
x_18 = lean_array_push(x_16, x_3);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_18);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_3);
x_24 = lean_array_push(x_23, x_3);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_5 = x_27;
x_6 = x_22;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_array_get_size(x_4);
x_34 = lean_nat_dec_le(x_33, x_32);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_31);
lean_dec(x_31);
x_37 = l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1(x_4, x_32, x_30, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_5 = x_38;
x_6 = x_29;
x_11 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_41, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unbox(x_31);
lean_dec(x_31);
x_46 = l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1(x_4, x_32, x_30, x_45, x_43, x_7, x_8, x_9, x_10, x_44);
lean_dec(x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_5 = x_47;
x_6 = x_29;
x_11 = x_48;
goto _start;
}
else
{
uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = 0;
x_16 = 1;
x_17 = 1;
lean_inc(x_1);
x_18 = l_Lean_Meta_mkLambdaFVars(x_1, x_9, x_15, x_16, x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_app___override(x_2, x_19);
x_22 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(x_3, x_4, x_5, x_6, x_7, x_1, x_8, x_21, x_10, x_11, x_12, x_13, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_20 = lean_array_to_list(lean_box(0), x_1);
x_21 = l_Lean_Expr_const___override(x_2, x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
x_22 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(x_3, x_4, x_5, x_21, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
if (x_12 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(x_6, x_23, x_3, x_7, x_8, x_9, x_10, x_11, x_13, x_15, x_16, x_17, x_18, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_10);
x_28 = lean_infer_type(x_10, x_15, x_16, x_17, x_18, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1;
lean_inc(x_10);
x_32 = lean_array_push(x_31, x_10);
lean_inc(x_17);
lean_inc(x_15);
x_33 = l_Lean_Expr_abstractM(x_13, x_32, x_15, x_16, x_17, x_18, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3;
x_37 = 0;
x_38 = l_Lean_Expr_lam___override(x_36, x_29, x_34, x_37);
x_39 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(x_6, x_26, x_3, x_7, x_8, x_9, x_10, x_11, x_38, x_15, x_16, x_17, x_18, x_35);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise is not of the form (C ...)", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recursor '", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' can only eliminate into Prop", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_List_redLength___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___rarg(x_22, x_24);
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
x_27 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___at_Lean_MVarId_induction___spec__6(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_1);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_39, x_17, x_18, x_19, x_20, x_32);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_33, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_41, x_17, x_18, x_19, x_20, x_42);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_33, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_48, x_17, x_18, x_19, x_20, x_32);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_3);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_box(0);
x_53 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_51, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_52, x_17, x_18, x_19, x_20, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_28);
if (x_54 == 0)
{
return x_28;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_28, 0);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_28);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 5:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_dec(x_14);
x_60 = lean_array_set(x_15, x_16, x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_16, x_61);
lean_dec(x_16);
x_14 = x_58;
x_15 = x_60;
x_16 = x_62;
goto _start;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3;
x_65 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_64, x_17, x_18, x_19, x_20, x_21);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l_Lean_MVarId_getType(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_20);
x_22 = l_Lean_Meta_getLevel(x_20, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_normalizeLevel(x_23, x_14, x_15, x_16, x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_14);
x_28 = l_Lean_FVarId_getDecl(x_2, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_LocalDecl_type(x_29);
lean_dec(x_29);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_31);
x_32 = l_Lean_Meta_whnfUntil(x_31, x_3, x_14, x_15, x_16, x_17, x_30);
lean_dec(x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_1, x_31, x_14, x_15, x_16, x_17, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_37, x_38);
x_40 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1, x_11, x_12, x_13, x_20, x_26, x_37, x_41, x_43, x_14, x_15, x_16, x_17, x_36);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_28);
if (x_49 == 0)
{
return x_28;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_28, 0);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_28);
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
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_19);
if (x_57 == 0)
{
return x_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_19);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_array_get_size(x_1);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_21, x_2, x_1);
lean_inc(x_3);
x_23 = l_Lean_Expr_fvar___override(x_3);
x_24 = lean_box(x_11);
lean_inc(x_4);
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___boxed), 18, 13);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_3);
lean_closure_set(x_25, 2, x_5);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_7);
lean_closure_set(x_25, 5, x_8);
lean_closure_set(x_25, 6, x_9);
lean_closure_set(x_25, 7, x_10);
lean_closure_set(x_25, 8, x_24);
lean_closure_set(x_25, 9, x_12);
lean_closure_set(x_25, 10, x_13);
lean_closure_set(x_25, 11, x_22);
lean_closure_set(x_25, 12, x_23);
x_26 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_4, x_25, x_15, x_16, x_17, x_18, x_19);
return x_26;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("after revert&intro\n", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_13);
x_19 = lean_array_get_size(x_1);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_1);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_20, x_2, x_1);
x_22 = lean_array_push(x_21, x_3);
x_23 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_24 = l_Lean_MVarId_revert(x_4, x_22, x_23, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_31 = l_Lean_Meta_introNCore(x_28, x_19, x_29, x_30, x_23, x_14, x_15, x_16, x_17, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_36 = l_Lean_Meta_intro1Core(x_35, x_23, x_14, x_15, x_16, x_17, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1;
x_42 = l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5(x_34, x_1, x_20, x_2, x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_58 = lean_st_ref_get(x_17, x_38);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_44 = x_30;
x_45 = x_62;
goto block_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
lean_inc(x_12);
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_12, x_14, x_15, x_16, x_17, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_44 = x_67;
x_45 = x_66;
goto block_57;
}
block_57:
{
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_12);
x_46 = lean_box(0);
x_47 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2(x_34, x_2, x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27, x_43, x_46, x_14, x_15, x_16, x_17, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_40);
x_48 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_48, 0, x_40);
x_49 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_12, x_52, x_14, x_15, x_16, x_17, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2(x_34, x_2, x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27, x_43, x_54, x_14, x_15, x_16, x_17, x_55);
lean_dec(x_54);
return x_56;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_36);
if (x_68 == 0)
{
return x_36;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_36, 0);
x_70 = lean_ctor_get(x_36, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_36);
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
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_31);
if (x_72 == 0)
{
return x_31;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_31, 0);
x_74 = lean_ctor_get(x_31, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_31);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_24);
if (x_76 == 0)
{
return x_24;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_24, 0);
x_78 = lean_ctor_get(x_24, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_24);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' does not support dependent elimination, but conclusion depends on major premise", 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_10);
x_18 = lean_ctor_get(x_7, 5);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_18, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 6);
lean_inc(x_21);
x_22 = l_List_redLength___rarg(x_21);
x_23 = lean_mk_empty_array_with_capacity(x_22);
lean_dec(x_22);
x_24 = l_List_toArrayAux___rarg(x_21, x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_26, x_27, x_24, x_13, x_14, x_15, x_16, x_20);
lean_dec(x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_1);
x_31 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_34 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_32, x_2, x_13, x_14, x_15, x_16, x_33);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_35 = x_56;
x_36 = x_55;
goto block_52;
}
else
{
uint8_t x_57; 
lean_dec(x_32);
x_57 = 0;
x_35 = x_57;
x_36 = x_33;
goto block_52;
}
block_52:
{
if (x_35 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_29, x_27, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_18, x_34, x_5, x_37, x_13, x_14, x_15, x_16, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_3);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_40 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_43, x_13, x_14, x_15, x_16, x_36);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_29, x_27, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_18, x_34, x_5, x_45, x_13, x_14, x_15, x_16, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_28);
if (x_62 == 0)
{
return x_28;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_28, 0);
x_64 = lean_ctor_get(x_28, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_19);
if (x_66 == 0)
{
return x_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_19, 0);
x_68 = lean_ctor_get(x_19, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_19);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 1:
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_12);
lean_dec(x_10);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_71 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_70, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_7, 6);
lean_inc(x_73);
x_74 = l_List_redLength___rarg(x_73);
x_75 = lean_mk_empty_array_with_capacity(x_74);
lean_dec(x_74);
x_76 = l_List_toArrayAux___rarg(x_73, x_75);
x_77 = lean_array_get_size(x_76);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_80 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_78, x_79, x_76, x_13, x_14, x_15, x_16, x_72);
lean_dec(x_11);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_1);
x_83 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_86 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_84, x_2, x_13, x_14, x_15, x_16, x_85);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_unbox(x_106);
lean_dec(x_106);
x_87 = x_108;
x_88 = x_107;
goto block_104;
}
else
{
uint8_t x_109; 
lean_dec(x_84);
x_109 = 0;
x_87 = x_109;
x_88 = x_85;
goto block_104;
}
block_104:
{
if (x_87 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_box(0);
x_90 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_81, x_79, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_70, x_86, x_5, x_89, x_13, x_14, x_15, x_16, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_3);
x_91 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_91, 0, x_3);
x_92 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_96 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_95, x_13, x_14, x_15, x_16, x_88);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_81, x_79, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_70, x_86, x_5, x_97, x_13, x_14, x_15, x_16, x_98);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_81);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_81);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_83);
if (x_110 == 0)
{
return x_83;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_83, 0);
x_112 = lean_ctor_get(x_83, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_83);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_80);
if (x_114 == 0)
{
return x_80;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_80, 0);
x_116 = lean_ctor_get(x_80, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_80);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_71);
if (x_118 == 0)
{
return x_71;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_71, 0);
x_120 = lean_ctor_get(x_71, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_71);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
case 2:
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_12);
lean_dec(x_10);
x_122 = lean_ctor_get(x_7, 5);
lean_inc(x_122);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_123 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_122, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; size_t x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_ctor_get(x_7, 6);
lean_inc(x_125);
x_126 = l_List_redLength___rarg(x_125);
x_127 = lean_mk_empty_array_with_capacity(x_126);
lean_dec(x_126);
x_128 = l_List_toArrayAux___rarg(x_125, x_127);
x_129 = lean_array_get_size(x_128);
x_130 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_131 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_132 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_130, x_131, x_128, x_13, x_14, x_15, x_16, x_124);
lean_dec(x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_1);
x_135 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_138 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_136, x_2, x_13, x_14, x_15, x_16, x_137);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_139 = x_160;
x_140 = x_159;
goto block_156;
}
else
{
uint8_t x_161; 
lean_dec(x_136);
x_161 = 0;
x_139 = x_161;
x_140 = x_137;
goto block_156;
}
block_156:
{
if (x_139 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
x_142 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_133, x_131, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_122, x_138, x_5, x_141, x_13, x_14, x_15, x_16, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_inc(x_3);
x_143 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_143, 0, x_3);
x_144 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_148 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_147, x_13, x_14, x_15, x_16, x_140);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_133, x_131, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_122, x_138, x_5, x_149, x_13, x_14, x_15, x_16, x_150);
return x_151;
}
else
{
uint8_t x_152; 
lean_dec(x_133);
lean_dec(x_122);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_148);
if (x_152 == 0)
{
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 0);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_148);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_133);
lean_dec(x_122);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_135);
if (x_162 == 0)
{
return x_135;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_135, 0);
x_164 = lean_ctor_get(x_135, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_135);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_122);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_132);
if (x_166 == 0)
{
return x_132;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_132, 0);
x_168 = lean_ctor_get(x_132, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_132);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_122);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_123);
if (x_170 == 0)
{
return x_123;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_123, 0);
x_172 = lean_ctor_get(x_123, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_123);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
case 3:
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_12);
lean_dec(x_10);
x_174 = lean_ctor_get(x_7, 5);
lean_inc(x_174);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_175 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_174, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; size_t x_182; size_t x_183; lean_object* x_184; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_ctor_get(x_7, 6);
lean_inc(x_177);
x_178 = l_List_redLength___rarg(x_177);
x_179 = lean_mk_empty_array_with_capacity(x_178);
lean_dec(x_178);
x_180 = l_List_toArrayAux___rarg(x_177, x_179);
x_181 = lean_array_get_size(x_180);
x_182 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_183 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_184 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_182, x_183, x_180, x_13, x_14, x_15, x_16, x_176);
lean_dec(x_11);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_1);
x_187 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_190 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_188, x_2, x_13, x_14, x_15, x_16, x_189);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_unbox(x_210);
lean_dec(x_210);
x_191 = x_212;
x_192 = x_211;
goto block_208;
}
else
{
uint8_t x_213; 
lean_dec(x_188);
x_213 = 0;
x_191 = x_213;
x_192 = x_189;
goto block_208;
}
block_208:
{
if (x_191 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_box(0);
x_194 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_185, x_183, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_174, x_190, x_5, x_193, x_13, x_14, x_15, x_16, x_192);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_inc(x_3);
x_195 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_195, 0, x_3);
x_196 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_197 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_200 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_199, x_13, x_14, x_15, x_16, x_192);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_185, x_183, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_174, x_190, x_5, x_201, x_13, x_14, x_15, x_16, x_202);
return x_203;
}
else
{
uint8_t x_204; 
lean_dec(x_185);
lean_dec(x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_200);
if (x_204 == 0)
{
return x_200;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_200, 0);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_200);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_185);
lean_dec(x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_187);
if (x_214 == 0)
{
return x_187;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_187, 0);
x_216 = lean_ctor_get(x_187, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_187);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_184);
if (x_218 == 0)
{
return x_184;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_184, 0);
x_220 = lean_ctor_get(x_184, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_184);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_175);
if (x_222 == 0)
{
return x_175;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_175, 0);
x_224 = lean_ctor_get(x_175, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_175);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
case 4:
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_12);
lean_dec(x_10);
x_226 = lean_ctor_get(x_7, 5);
lean_inc(x_226);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_227 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_226, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; size_t x_234; size_t x_235; lean_object* x_236; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get(x_7, 6);
lean_inc(x_229);
x_230 = l_List_redLength___rarg(x_229);
x_231 = lean_mk_empty_array_with_capacity(x_230);
lean_dec(x_230);
x_232 = l_List_toArrayAux___rarg(x_229, x_231);
x_233 = lean_array_get_size(x_232);
x_234 = lean_usize_of_nat(x_233);
lean_dec(x_233);
x_235 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_236 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_234, x_235, x_232, x_13, x_14, x_15, x_16, x_228);
lean_dec(x_11);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
lean_inc(x_1);
x_239 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_242 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_261 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_240, x_2, x_13, x_14, x_15, x_16, x_241);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_unbox(x_262);
lean_dec(x_262);
x_243 = x_264;
x_244 = x_263;
goto block_260;
}
else
{
uint8_t x_265; 
lean_dec(x_240);
x_265 = 0;
x_243 = x_265;
x_244 = x_241;
goto block_260;
}
block_260:
{
if (x_243 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_box(0);
x_246 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_237, x_235, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_226, x_242, x_5, x_245, x_13, x_14, x_15, x_16, x_244);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_inc(x_3);
x_247 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_247, 0, x_3);
x_248 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_249 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_251 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_252 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_251, x_13, x_14, x_15, x_16, x_244);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_237, x_235, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_226, x_242, x_5, x_253, x_13, x_14, x_15, x_16, x_254);
return x_255;
}
else
{
uint8_t x_256; 
lean_dec(x_237);
lean_dec(x_226);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_252);
if (x_256 == 0)
{
return x_252;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_252, 0);
x_258 = lean_ctor_get(x_252, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_252);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_237);
lean_dec(x_226);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_239);
if (x_266 == 0)
{
return x_239;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_239, 0);
x_268 = lean_ctor_get(x_239, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_239);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_226);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_236);
if (x_270 == 0)
{
return x_236;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_236, 0);
x_272 = lean_ctor_get(x_236, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_236);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_226);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_227);
if (x_274 == 0)
{
return x_227;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_227, 0);
x_276 = lean_ctor_get(x_227, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_227);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
case 5:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_10, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_10, 1);
lean_inc(x_279);
lean_dec(x_10);
x_280 = lean_array_set(x_11, x_12, x_279);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_sub(x_12, x_281);
lean_dec(x_12);
x_10 = x_278;
x_11 = x_280;
x_12 = x_282;
goto _start;
}
case 6:
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_12);
lean_dec(x_10);
x_284 = lean_ctor_get(x_7, 5);
lean_inc(x_284);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_285 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_284, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; size_t x_292; size_t x_293; lean_object* x_294; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = lean_ctor_get(x_7, 6);
lean_inc(x_287);
x_288 = l_List_redLength___rarg(x_287);
x_289 = lean_mk_empty_array_with_capacity(x_288);
lean_dec(x_288);
x_290 = l_List_toArrayAux___rarg(x_287, x_289);
x_291 = lean_array_get_size(x_290);
x_292 = lean_usize_of_nat(x_291);
lean_dec(x_291);
x_293 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_294 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_292, x_293, x_290, x_13, x_14, x_15, x_16, x_286);
lean_dec(x_11);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_1);
x_297 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_296);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_300 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_319 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_298, x_2, x_13, x_14, x_15, x_16, x_299);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_unbox(x_320);
lean_dec(x_320);
x_301 = x_322;
x_302 = x_321;
goto block_318;
}
else
{
uint8_t x_323; 
lean_dec(x_298);
x_323 = 0;
x_301 = x_323;
x_302 = x_299;
goto block_318;
}
block_318:
{
if (x_301 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_box(0);
x_304 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_295, x_293, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_284, x_300, x_5, x_303, x_13, x_14, x_15, x_16, x_302);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_inc(x_3);
x_305 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_305, 0, x_3);
x_306 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
x_308 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_310 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_309, x_13, x_14, x_15, x_16, x_302);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_295, x_293, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_284, x_300, x_5, x_311, x_13, x_14, x_15, x_16, x_312);
return x_313;
}
else
{
uint8_t x_314; 
lean_dec(x_295);
lean_dec(x_284);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_310);
if (x_314 == 0)
{
return x_310;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_310, 0);
x_316 = lean_ctor_get(x_310, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_310);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_295);
lean_dec(x_284);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_297);
if (x_324 == 0)
{
return x_297;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_297, 0);
x_326 = lean_ctor_get(x_297, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_297);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_284);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_294);
if (x_328 == 0)
{
return x_294;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_294, 0);
x_330 = lean_ctor_get(x_294, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_294);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_284);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_285);
if (x_332 == 0)
{
return x_285;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_285, 0);
x_334 = lean_ctor_get(x_285, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_285);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
case 7:
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_12);
lean_dec(x_10);
x_336 = lean_ctor_get(x_7, 5);
lean_inc(x_336);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_337 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_336, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; size_t x_344; size_t x_345; lean_object* x_346; 
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = lean_ctor_get(x_7, 6);
lean_inc(x_339);
x_340 = l_List_redLength___rarg(x_339);
x_341 = lean_mk_empty_array_with_capacity(x_340);
lean_dec(x_340);
x_342 = l_List_toArrayAux___rarg(x_339, x_341);
x_343 = lean_array_get_size(x_342);
x_344 = lean_usize_of_nat(x_343);
lean_dec(x_343);
x_345 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_346 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_344, x_345, x_342, x_13, x_14, x_15, x_16, x_338);
lean_dec(x_11);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_1);
x_349 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_348);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; lean_object* x_354; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_352 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_371 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_350, x_2, x_13, x_14, x_15, x_16, x_351);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
x_374 = lean_unbox(x_372);
lean_dec(x_372);
x_353 = x_374;
x_354 = x_373;
goto block_370;
}
else
{
uint8_t x_375; 
lean_dec(x_350);
x_375 = 0;
x_353 = x_375;
x_354 = x_351;
goto block_370;
}
block_370:
{
if (x_353 == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_box(0);
x_356 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_347, x_345, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_336, x_352, x_5, x_355, x_13, x_14, x_15, x_16, x_354);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_inc(x_3);
x_357 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_357, 0, x_3);
x_358 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_359 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_361 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_362 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_361, x_13, x_14, x_15, x_16, x_354);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_347, x_345, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_336, x_352, x_5, x_363, x_13, x_14, x_15, x_16, x_364);
return x_365;
}
else
{
uint8_t x_366; 
lean_dec(x_347);
lean_dec(x_336);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_366 = !lean_is_exclusive(x_362);
if (x_366 == 0)
{
return x_362;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_362, 0);
x_368 = lean_ctor_get(x_362, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_362);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
}
}
else
{
uint8_t x_376; 
lean_dec(x_347);
lean_dec(x_336);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_349);
if (x_376 == 0)
{
return x_349;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_349, 0);
x_378 = lean_ctor_get(x_349, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_349);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
else
{
uint8_t x_380; 
lean_dec(x_336);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_380 = !lean_is_exclusive(x_346);
if (x_380 == 0)
{
return x_346;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_346, 0);
x_382 = lean_ctor_get(x_346, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_346);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_336);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_384 = !lean_is_exclusive(x_337);
if (x_384 == 0)
{
return x_337;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_337, 0);
x_386 = lean_ctor_get(x_337, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_337);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
case 8:
{
lean_object* x_388; lean_object* x_389; 
lean_dec(x_12);
lean_dec(x_10);
x_388 = lean_ctor_get(x_7, 5);
lean_inc(x_388);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_389 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_388, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; size_t x_396; size_t x_397; lean_object* x_398; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
x_391 = lean_ctor_get(x_7, 6);
lean_inc(x_391);
x_392 = l_List_redLength___rarg(x_391);
x_393 = lean_mk_empty_array_with_capacity(x_392);
lean_dec(x_392);
x_394 = l_List_toArrayAux___rarg(x_391, x_393);
x_395 = lean_array_get_size(x_394);
x_396 = lean_usize_of_nat(x_395);
lean_dec(x_395);
x_397 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_398 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_396, x_397, x_394, x_13, x_14, x_15, x_16, x_390);
lean_dec(x_11);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_1);
x_401 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_404 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_423 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_402, x_2, x_13, x_14, x_15, x_16, x_403);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_unbox(x_424);
lean_dec(x_424);
x_405 = x_426;
x_406 = x_425;
goto block_422;
}
else
{
uint8_t x_427; 
lean_dec(x_402);
x_427 = 0;
x_405 = x_427;
x_406 = x_403;
goto block_422;
}
block_422:
{
if (x_405 == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_box(0);
x_408 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_399, x_397, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_388, x_404, x_5, x_407, x_13, x_14, x_15, x_16, x_406);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_inc(x_3);
x_409 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_409, 0, x_3);
x_410 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_411 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
x_412 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_413 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_414 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_413, x_13, x_14, x_15, x_16, x_406);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_399, x_397, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_388, x_404, x_5, x_415, x_13, x_14, x_15, x_16, x_416);
return x_417;
}
else
{
uint8_t x_418; 
lean_dec(x_399);
lean_dec(x_388);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_418 = !lean_is_exclusive(x_414);
if (x_418 == 0)
{
return x_414;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_414, 0);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_414);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
}
}
else
{
uint8_t x_428; 
lean_dec(x_399);
lean_dec(x_388);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_428 = !lean_is_exclusive(x_401);
if (x_428 == 0)
{
return x_401;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_401, 0);
x_430 = lean_ctor_get(x_401, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_401);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
uint8_t x_432; 
lean_dec(x_388);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_432 = !lean_is_exclusive(x_398);
if (x_432 == 0)
{
return x_398;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_398, 0);
x_434 = lean_ctor_get(x_398, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_398);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_388);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_436 = !lean_is_exclusive(x_389);
if (x_436 == 0)
{
return x_389;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_389, 0);
x_438 = lean_ctor_get(x_389, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_389);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
case 9:
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_12);
lean_dec(x_10);
x_440 = lean_ctor_get(x_7, 5);
lean_inc(x_440);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_441 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_440, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; size_t x_448; size_t x_449; lean_object* x_450; 
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_ctor_get(x_7, 6);
lean_inc(x_443);
x_444 = l_List_redLength___rarg(x_443);
x_445 = lean_mk_empty_array_with_capacity(x_444);
lean_dec(x_444);
x_446 = l_List_toArrayAux___rarg(x_443, x_445);
x_447 = lean_array_get_size(x_446);
x_448 = lean_usize_of_nat(x_447);
lean_dec(x_447);
x_449 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_450 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_448, x_449, x_446, x_13, x_14, x_15, x_16, x_442);
lean_dec(x_11);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_inc(x_1);
x_453 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_452);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; uint8_t x_456; uint8_t x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_456 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_475 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_454, x_2, x_13, x_14, x_15, x_16, x_455);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_unbox(x_476);
lean_dec(x_476);
x_457 = x_478;
x_458 = x_477;
goto block_474;
}
else
{
uint8_t x_479; 
lean_dec(x_454);
x_479 = 0;
x_457 = x_479;
x_458 = x_455;
goto block_474;
}
block_474:
{
if (x_457 == 0)
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_box(0);
x_460 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_451, x_449, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_440, x_456, x_5, x_459, x_13, x_14, x_15, x_16, x_458);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_inc(x_3);
x_461 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_461, 0, x_3);
x_462 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_463 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_461);
x_464 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_465 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_466 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_465, x_13, x_14, x_15, x_16, x_458);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_451, x_449, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_440, x_456, x_5, x_467, x_13, x_14, x_15, x_16, x_468);
return x_469;
}
else
{
uint8_t x_470; 
lean_dec(x_451);
lean_dec(x_440);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_470 = !lean_is_exclusive(x_466);
if (x_470 == 0)
{
return x_466;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_466, 0);
x_472 = lean_ctor_get(x_466, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_466);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_451);
lean_dec(x_440);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_453);
if (x_480 == 0)
{
return x_453;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_453, 0);
x_482 = lean_ctor_get(x_453, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_453);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_440);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_484 = !lean_is_exclusive(x_450);
if (x_484 == 0)
{
return x_450;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_450, 0);
x_486 = lean_ctor_get(x_450, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_450);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_440);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_488 = !lean_is_exclusive(x_441);
if (x_488 == 0)
{
return x_441;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_441, 0);
x_490 = lean_ctor_get(x_441, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_441);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
case 10:
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_12);
lean_dec(x_10);
x_492 = lean_ctor_get(x_7, 5);
lean_inc(x_492);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_493 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_492, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; size_t x_500; size_t x_501; lean_object* x_502; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get(x_7, 6);
lean_inc(x_495);
x_496 = l_List_redLength___rarg(x_495);
x_497 = lean_mk_empty_array_with_capacity(x_496);
lean_dec(x_496);
x_498 = l_List_toArrayAux___rarg(x_495, x_497);
x_499 = lean_array_get_size(x_498);
x_500 = lean_usize_of_nat(x_499);
lean_dec(x_499);
x_501 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_502 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_500, x_501, x_498, x_13, x_14, x_15, x_16, x_494);
lean_dec(x_11);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
lean_inc(x_1);
x_505 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; uint8_t x_509; lean_object* x_510; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_508 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_527 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_506, x_2, x_13, x_14, x_15, x_16, x_507);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_unbox(x_528);
lean_dec(x_528);
x_509 = x_530;
x_510 = x_529;
goto block_526;
}
else
{
uint8_t x_531; 
lean_dec(x_506);
x_531 = 0;
x_509 = x_531;
x_510 = x_507;
goto block_526;
}
block_526:
{
if (x_509 == 0)
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_box(0);
x_512 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_503, x_501, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_492, x_508, x_5, x_511, x_13, x_14, x_15, x_16, x_510);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_inc(x_3);
x_513 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_513, 0, x_3);
x_514 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_515 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
x_516 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_517 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_518 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_517, x_13, x_14, x_15, x_16, x_510);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_503, x_501, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_492, x_508, x_5, x_519, x_13, x_14, x_15, x_16, x_520);
return x_521;
}
else
{
uint8_t x_522; 
lean_dec(x_503);
lean_dec(x_492);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_522 = !lean_is_exclusive(x_518);
if (x_522 == 0)
{
return x_518;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_518, 0);
x_524 = lean_ctor_get(x_518, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_518);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
}
}
else
{
uint8_t x_532; 
lean_dec(x_503);
lean_dec(x_492);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_532 = !lean_is_exclusive(x_505);
if (x_532 == 0)
{
return x_505;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_505, 0);
x_534 = lean_ctor_get(x_505, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_505);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
else
{
uint8_t x_536; 
lean_dec(x_492);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_536 = !lean_is_exclusive(x_502);
if (x_536 == 0)
{
return x_502;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_502, 0);
x_538 = lean_ctor_get(x_502, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_502);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
}
}
else
{
uint8_t x_540; 
lean_dec(x_492);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_540 = !lean_is_exclusive(x_493);
if (x_540 == 0)
{
return x_493;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_493, 0);
x_542 = lean_ctor_get(x_493, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_493);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
default: 
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_12);
lean_dec(x_10);
x_544 = lean_ctor_get(x_7, 5);
lean_inc(x_544);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_545 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_544, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; size_t x_552; size_t x_553; lean_object* x_554; 
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
lean_dec(x_545);
x_547 = lean_ctor_get(x_7, 6);
lean_inc(x_547);
x_548 = l_List_redLength___rarg(x_547);
x_549 = lean_mk_empty_array_with_capacity(x_548);
lean_dec(x_548);
x_550 = l_List_toArrayAux___rarg(x_547, x_549);
x_551 = lean_array_get_size(x_550);
x_552 = lean_usize_of_nat(x_551);
lean_dec(x_551);
x_553 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_554 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_552, x_553, x_550, x_13, x_14, x_15, x_16, x_546);
lean_dec(x_11);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
lean_inc(x_1);
x_557 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; uint8_t x_560; uint8_t x_561; lean_object* x_562; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_560 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_579 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_558, x_2, x_13, x_14, x_15, x_16, x_559);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = lean_unbox(x_580);
lean_dec(x_580);
x_561 = x_582;
x_562 = x_581;
goto block_578;
}
else
{
uint8_t x_583; 
lean_dec(x_558);
x_583 = 0;
x_561 = x_583;
x_562 = x_559;
goto block_578;
}
block_578:
{
if (x_561 == 0)
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_box(0);
x_564 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_555, x_553, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_544, x_560, x_5, x_563, x_13, x_14, x_15, x_16, x_562);
return x_564;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_inc(x_3);
x_565 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_565, 0, x_3);
x_566 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6;
x_567 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_565);
x_568 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2;
x_569 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_6);
x_570 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_569, x_13, x_14, x_15, x_16, x_562);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_555, x_553, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_544, x_560, x_5, x_571, x_13, x_14, x_15, x_16, x_572);
return x_573;
}
else
{
uint8_t x_574; 
lean_dec(x_555);
lean_dec(x_544);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_574 = !lean_is_exclusive(x_570);
if (x_574 == 0)
{
return x_570;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_570, 0);
x_576 = lean_ctor_get(x_570, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_570);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
return x_577;
}
}
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_555);
lean_dec(x_544);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_557);
if (x_584 == 0)
{
return x_557;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_557, 0);
x_586 = lean_ctor_get(x_557, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_557);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
else
{
uint8_t x_588; 
lean_dec(x_544);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_588 = !lean_is_exclusive(x_554);
if (x_588 == 0)
{
return x_554;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_554, 0);
x_590 = lean_ctor_get(x_554, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_554);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_544);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_592 = !lean_is_exclusive(x_545);
if (x_592 == 0)
{
return x_545;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_545, 0);
x_594 = lean_ctor_get(x_545, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_545);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_MVarId_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_FVarId_getDecl(x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_19 = l_Lean_Meta_mkRecursorInfo(x_3, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
x_24 = l_Lean_Meta_whnfUntil(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_1, x_22, x_7, x_8, x_9, x_10, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_29, x_30);
x_32 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_29);
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_12, x_20, x_23, x_29, x_29, x_33, x_35, x_7, x_8, x_9, x_10, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_induction___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initial\n", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_induction___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_st_ref_get(x_9, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = 0;
x_11 = x_30;
x_12 = x_29;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
lean_inc(x_5);
x_32 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_5, x_6, x_7, x_8, x_9, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
x_11 = x_35;
x_12 = x_34;
goto block_24;
}
block_24:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_MVarId_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_13, x_6, x_7, x_8, x_9, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_MVarId_induction___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_5);
x_20 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_5, x_19, x_6, x_7, x_8, x_9, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_MVarId_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_21, x_6, x_7, x_8, x_9, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_induction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_induction___closed__2;
x_2 = l_Lean_MVarId_induction___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_induction___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_MVarId_induction___closed__5;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lambda__2), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_10);
x_12 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_MVarId_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_MVarId_induction___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_List_foldlM___at_Lean_MVarId_induction___spec__6___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_MVarId_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_21 = lean_unbox(x_11);
lean_dec(x_11);
x_22 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__2(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
size_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_11);
lean_dec(x_11);
x_21 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_induction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3484_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MVarId_induction___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8);
l_Lean_Meta_InductionSubgoal_fields___default___closed__1 = _init_l_Lean_Meta_InductionSubgoal_fields___default___closed__1();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_fields___default___closed__1);
l_Lean_Meta_InductionSubgoal_fields___default = _init_l_Lean_Meta_InductionSubgoal_fields___default();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_fields___default);
l_Lean_Meta_InductionSubgoal_subst___default = _init_l_Lean_Meta_InductionSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_subst___default);
l_Lean_Meta_instInhabitedInductionSubgoal___closed__1 = _init_l_Lean_Meta_instInhabitedInductionSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedInductionSubgoal___closed__1);
l_Lean_Meta_instInhabitedInductionSubgoal = _init_l_Lean_Meta_instInhabitedInductionSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedInductionSubgoal);
l_Lean_Meta_AltVarNames_explicit___default = _init_l_Lean_Meta_AltVarNames_explicit___default();
l_Lean_Meta_AltVarNames_varNames___default = _init_l_Lean_Meta_AltVarNames_varNames___default();
lean_mark_persistent(l_Lean_Meta_AltVarNames_varNames___default);
l_Lean_Meta_instInhabitedAltVarNames___closed__1 = _init_l_Lean_Meta_instInhabitedAltVarNames___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedAltVarNames___closed__1);
l_Lean_Meta_instInhabitedAltVarNames = _init_l_Lean_Meta_instInhabitedAltVarNames();
lean_mark_persistent(l_Lean_Meta_instInhabitedAltVarNames);
l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1);
l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1 = _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__1);
l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2 = _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2();
lean_mark_persistent(l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__2);
l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3 = _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3();
lean_mark_persistent(l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__3);
l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4 = _init_l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4();
lean_mark_persistent(l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___closed__4);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4);
l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1 = _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1();
lean_mark_persistent(l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1);
l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2 = _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2();
lean_mark_persistent(l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__3);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__1___closed__4);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__4___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__4);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__5);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__7);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__8);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___lambda__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__8___closed__2);
l_Lean_MVarId_induction___lambda__2___closed__1 = _init_l_Lean_MVarId_induction___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_induction___lambda__2___closed__1);
l_Lean_MVarId_induction___lambda__2___closed__2 = _init_l_Lean_MVarId_induction___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_induction___lambda__2___closed__2);
l_Lean_MVarId_induction___closed__1 = _init_l_Lean_MVarId_induction___closed__1();
lean_mark_persistent(l_Lean_MVarId_induction___closed__1);
l_Lean_MVarId_induction___closed__2 = _init_l_Lean_MVarId_induction___closed__2();
lean_mark_persistent(l_Lean_MVarId_induction___closed__2);
l_Lean_MVarId_induction___closed__3 = _init_l_Lean_MVarId_induction___closed__3();
lean_mark_persistent(l_Lean_MVarId_induction___closed__3);
l_Lean_MVarId_induction___closed__4 = _init_l_Lean_MVarId_induction___closed__4();
lean_mark_persistent(l_Lean_MVarId_induction___closed__4);
l_Lean_MVarId_induction___closed__5 = _init_l_Lean_MVarId_induction___closed__5();
lean_mark_persistent(l_Lean_MVarId_induction___closed__5);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3484_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
