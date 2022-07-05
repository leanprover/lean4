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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_induction___closed__1;
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3;
static lean_object* l_Lean_Meta_induction___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
static lean_object* l_Lean_Meta_induction___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3;
static lean_object* l_Lean_Meta_induction___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_fields___default;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInductionSubgoal;
static lean_object* l_Lean_Meta_induction___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3288_(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___boxed(lean_object**);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_induction___closed__5;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAltVarNames;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_subst___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedInductionSubgoal___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAltVarNames___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object**);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___boxed(lean_object**);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2___boxed(lean_object**);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AltVarNames_varNames___default;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object**);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object*);
static lean_object* l_List_forM___at_Lean_Meta_induction___spec__1___closed__2;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forM___at_Lean_Meta_induction___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_induction___closed__4;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1;
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_induction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___boxed(lean_object**);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
lean_object* l_Lean_exprDependsOn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
lean_object* l_Lean_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_AltVarNames_explicit___default;
LEAN_EXPORT lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLevel;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_11 = l_Lean_mkApp(x_1, x_5);
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
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_1, x_27, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_35 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_34, x_1, x_35, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_6);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_array_get_size(x_2);
x_48 = lean_nat_dec_lt(x_46, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
x_49 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_50 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_49, x_1, x_50, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_fget(x_2, x_46);
lean_dec(x_46);
x_53 = l_Lean_mkApp(x_4, x_52);
x_3 = x_45;
x_4 = x_53;
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
lean_dec(x_7);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_add(x_11, x_10);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_12);
x_14 = lean_nat_add(x_3, x_10);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_Lean_instInhabitedFVarId;
x_17 = lean_array_get(x_16, x_1, x_13);
x_18 = lean_nat_sub(x_13, x_3);
lean_dec(x_13);
x_19 = lean_nat_sub(x_18, x_10);
lean_dec(x_18);
x_20 = lean_array_get(x_16, x_4, x_19);
lean_dec(x_19);
x_21 = l_Lean_mkFVar(x_20);
x_22 = l_Lean_Meta_FVarSubst_insert(x_7, x_17, x_21);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_13);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
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
x_16 = l_Lean_mkApp(x_14, x_12);
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
x_29 = l_Lean_mkApp(x_27, x_12);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_assignExprMVar(x_1, x_2, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_18);
x_19 = lean_st_ref_set(x_6, x_13, x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_28 = l_Lean_assignExprMVar(x_1, x_2, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
x_31 = lean_st_ref_set(x_6, x_30, x_14);
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
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_32);
return x_34;
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
x_35 = l_Lean_mkApp(x_5, x_33);
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
lean_dec(x_33);
lean_inc(x_8);
x_40 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_41 = l_Lean_Meta_tryClear(x_39, x_40, x_21, x_22, x_23, x_24, x_38);
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
x_59 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_3, x_4, x_28, x_57, x_27, x_27, x_9);
lean_dec(x_27);
lean_dec(x_57);
lean_dec(x_28);
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
lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_40; uint8_t x_41; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_26 = l_Lean_Expr_headBeta(x_24);
x_40 = (uint8_t)((x_25 << 24) >> 61);
x_41 = l_Lean_BinderInfo_isInstImplicit(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_27 = x_42;
goto block_39;
}
else
{
uint8_t x_43; 
x_43 = l_Array_isEmpty___rarg(x_12);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_27 = x_44;
goto block_39;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
x_46 = l_Lean_Meta_synthInstance_x3f(x_26, x_45, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Name_append(x_16, x_23);
lean_dec(x_16);
lean_inc(x_18);
x_50 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_49, x_18, x_19, x_20, x_21, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
x_53 = l_Lean_mkApp(x_5, x_51);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_54 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_51, x_18, x_19, x_20, x_21, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_9, x_57);
lean_dec(x_9);
x_59 = lean_nat_add(x_10, x_57);
lean_dec(x_10);
x_60 = l_Lean_Expr_mvarId_x21(x_51);
lean_dec(x_51);
x_61 = lean_box(0);
x_62 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = lean_array_push(x_11, x_63);
x_65 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_58, x_59, x_53, x_55, x_15, x_64, x_18, x_19, x_20, x_21, x_56);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_53);
lean_dec(x_51);
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
x_66 = !lean_is_exclusive(x_54);
if (x_66 == 0)
{
return x_54;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_16);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec(x_47);
lean_inc(x_71);
x_72 = l_Lean_mkApp(x_5, x_71);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_73 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_71, x_18, x_19, x_20, x_21, x_70);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_9, x_76);
lean_dec(x_9);
x_78 = lean_nat_add(x_10, x_76);
lean_dec(x_10);
x_79 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_77, x_78, x_72, x_74, x_15, x_11, x_18, x_19, x_20, x_21, x_75);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_72);
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
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
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
x_84 = !lean_is_exclusive(x_46);
if (x_84 == 0)
{
return x_46;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_46, 0);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_46);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
block_39:
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_14);
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
x_32 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_6, x_33, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
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
x_88 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
x_89 = l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(x_88, x_18, x_19, x_20, x_21, x_22);
return x_89;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_35 = l_Lean_Expr_isForall(x_22);
if (x_35 == 0)
{
lean_object* x_36; 
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
x_36 = lean_box(0);
x_24 = x_36;
goto block_34;
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
lean_object* x_39; 
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
x_39 = lean_box(0);
x_24 = x_39;
goto block_34;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_41 = lean_nat_dec_eq(x_10, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_1);
x_42 = l_Lean_Meta_getMVarTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_dec_le(x_9, x_11);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_22, x_8, x_4, x_6, x_12, x_1, x_5, x_7, x_10, x_11, x_15, x_2, x_3, x_9, x_14, x_43, x_46, x_16, x_17, x_18, x_19, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_43);
lean_dec(x_22);
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
x_48 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_49 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_50 = l_Lean_Meta_throwTacticEx___rarg(x_48, x_1, x_49, x_16, x_17, x_18, x_19, x_44);
lean_dec(x_19);
lean_dec(x_17);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_inc(x_22);
lean_inc(x_12);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_22);
x_60 = lean_array_get_size(x_6);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_inc(x_5);
x_63 = l_Lean_mkApp(x_12, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_64 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_22, x_5, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_10, x_67);
lean_dec(x_10);
x_69 = lean_nat_add(x_68, x_60);
lean_dec(x_60);
lean_dec(x_68);
x_70 = 1;
x_10 = x_69;
x_12 = x_63;
x_13 = x_65;
x_14 = x_70;
x_20 = x_66;
goto _start;
}
else
{
uint8_t x_72; 
lean_dec(x_63);
lean_dec(x_60);
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
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
return x_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_64, 0);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_64);
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
x_76 = lean_nat_dec_le(x_60, x_60);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_59);
lean_inc(x_5);
x_77 = l_Lean_mkApp(x_12, x_5);
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
x_83 = lean_nat_add(x_82, x_60);
lean_dec(x_60);
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
lean_dec(x_60);
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
size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_22);
lean_dec(x_12);
x_90 = 0;
x_91 = lean_usize_of_nat(x_60);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_92 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_6, x_90, x_91, x_59, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_5);
x_97 = l_Lean_mkApp(x_95, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_98 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_96, x_5, x_16, x_17, x_18, x_19, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_10, x_101);
lean_dec(x_10);
x_103 = lean_nat_add(x_102, x_60);
lean_dec(x_60);
lean_dec(x_102);
x_104 = 1;
x_10 = x_103;
x_12 = x_97;
x_13 = x_99;
x_14 = x_104;
x_20 = x_100;
goto _start;
}
else
{
uint8_t x_106; 
lean_dec(x_97);
lean_dec(x_60);
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
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_60);
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
x_110 = !lean_is_exclusive(x_92);
if (x_110 == 0)
{
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
}
}
block_34:
{
lean_dec(x_24);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_12);
x_25 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_27 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_32, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_33;
}
}
}
else
{
uint8_t x_114; 
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
x_114 = !lean_is_exclusive(x_21);
if (x_114 == 0)
{
return x_21;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_21, 0);
x_116 = lean_ctor_get(x_21, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_21);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
x_14 = l_Lean_Meta_getMVarType(x_1, x_9, x_10, x_11, x_12, x_13);
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
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_List_forM___at_Lean_Meta_induction___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type is ill-formed", 32);
return x_1;
}
}
static lean_object* _init_l_List_forM___at_Lean_Meta_induction___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at_Lean_Meta_induction___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = l_Lean_indentExpr(x_3);
x_22 = l_List_forM___at_Lean_Meta_induction___spec__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_6, x_7, x_8, x_9, x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it depends on index occurring at position #", 79);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
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
x_18 = l_List_elem___at_Lean_Meta_induction___spec__2(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
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
lean_dec(x_11);
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
x_25 = l_Lean_Meta_getLocalDecl(x_24, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_fvarId_x21(x_4);
x_29 = lean_st_ref_get(x_12, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_10, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = l_Lean_localDeclDependsOn(x_26, x_28, x_35);
lean_dec(x_28);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_38);
x_39 = lean_st_ref_set(x_10, x_32, x_33);
x_40 = lean_unbox(x_37);
lean_dec(x_37);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_5);
x_49 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_2, x_53);
x_55 = l_Nat_repr(x_54);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_60, x_9, x_10, x_11, x_12, x_47);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_ctor_get(x_32, 0);
x_63 = lean_ctor_get(x_32, 1);
x_64 = lean_ctor_get(x_32, 2);
x_65 = lean_ctor_get(x_32, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_32);
x_66 = l_Lean_localDeclDependsOn(x_26, x_28, x_62);
lean_dec(x_28);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
x_70 = lean_st_ref_set(x_10, x_69, x_33);
x_71 = lean_unbox(x_67);
lean_dec(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_5);
x_78 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_2, x_82);
x_84 = l_Nat_repr(x_83);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
x_88 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_89, x_9, x_10, x_11, x_12, x_76);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
return x_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_25, 0);
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_25);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs in previous arguments", 67);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_17 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_5);
x_18 = l_Lean_Expr_fvarId_x21(x_5);
x_19 = lean_st_ref_get(x_13, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_11, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_4);
x_26 = l_Lean_exprDependsOn(x_4, x_18, x_25);
lean_dec(x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_28);
x_29 = lean_st_ref_set(x_11, x_22, x_23);
x_30 = lean_unbox(x_27);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_13);
lean_dec(x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_4);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_5);
x_36 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_8);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_43, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_13);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
x_51 = lean_ctor_get(x_22, 2);
x_52 = lean_ctor_get(x_22, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
lean_inc(x_4);
x_53 = l_Lean_exprDependsOn(x_4, x_18, x_49);
lean_dec(x_18);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
x_57 = lean_st_ref_set(x_11, x_56, x_23);
x_58 = lean_unbox(x_54);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_8);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
x_61 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_60, x_10, x_11, x_12, x_13, x_59);
lean_dec(x_13);
lean_dec(x_11);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_4);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_5);
x_64 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_indentExpr(x_8);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_71, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_13);
lean_dec(x_11);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs more than once", 60);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_9, x_17);
lean_dec(x_9);
x_19 = lean_nat_sub(x_8, x_18);
x_20 = lean_nat_sub(x_19, x_17);
lean_dec(x_19);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get(x_21, x_5, x_20);
x_23 = lean_nat_dec_eq(x_20, x_6);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_eqv(x_22, x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_26 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2(x_6, x_20, x_3, x_22, x_7, x_2, x_1, x_4, x_25, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_9 = x_18;
x_14 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
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
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_7);
x_34 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_indentExpr(x_4);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_41, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
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
x_47 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_48 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2(x_6, x_20, x_3, x_22, x_7, x_2, x_1, x_4, x_47, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_9 = x_18;
x_14 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
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
lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_14);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_get_size(x_1);
lean_inc(x_14);
lean_inc(x_7);
x_15 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3(x_2, x_3, x_4, x_5, x_1, x_6, x_7, x_14, x_14, x_9, x_10, x_11, x_12, x_13);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type index ", 25);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not a variable", 18);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_1, x_2);
x_15 = l_Lean_Expr_isFVar(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_6);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_3, x_24, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1(x_1, x_3, x_4, x_5, x_6, x_2, x_14, x_30, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_22 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2(x_5, x_16, x_1, x_2, x_3, x_4, x_21, x_9, x_10, x_11, x_12, x_13);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_33 = l_Lean_indentExpr(x_4);
x_34 = l_List_forM___at_Lean_Meta_induction___spec__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_37, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Expr_fvarId_x21(x_7);
x_11 = l_Lean_instInhabitedFVarId;
x_12 = lean_array_get(x_11, x_1, x_8);
x_13 = l_Lean_mkFVar(x_12);
x_14 = l_Lean_Meta_FVarSubst_insert(x_9, x_10, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
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
x_37 = l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1(x_4, x_32, x_30, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_3);
x_41 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_41, x_7, x_8, x_9, x_10, x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_21 = l_Lean_mkApp(x_2, x_19);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_20 = lean_array_to_list(lean_box(0), x_1);
x_21 = l_Lean_mkConst(x_2, x_20);
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
x_25 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__1(x_6, x_23, x_3, x_7, x_8, x_9, x_10, x_11, x_13, x_15, x_16, x_17, x_18, x_24);
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
x_31 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1;
lean_inc(x_10);
x_32 = lean_array_push(x_31, x_10);
lean_inc(x_17);
lean_inc(x_15);
x_33 = l_Lean_Meta_abstract(x_13, x_32, x_15, x_16, x_17, x_18, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3;
x_37 = 0;
x_38 = l_Lean_mkLambda(x_36, x_37, x_29, x_34);
x_39 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__1(x_6, x_26, x_3, x_7, x_8, x_9, x_10, x_11, x_38, x_15, x_16, x_17, x_18, x_35);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise is not of the form (C ...)", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4() {
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recursor '", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' can only eliminate into Prop", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
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
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4;
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___at_Lean_Meta_induction___spec__6(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_39, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_18);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2(x_33, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_45, x_17, x_18, x_19, x_20, x_32);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_3);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2(x_48, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_49, x_17, x_18, x_19, x_20, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
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
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 5:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_dec(x_14);
x_57 = lean_array_set(x_15, x_16, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_16, x_58);
lean_dec(x_16);
x_14 = x_55;
x_15 = x_57;
x_16 = x_59;
goto _start;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
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
x_61 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3;
x_62 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_61, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_18);
return x_62;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_18);
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
x_28 = l_Lean_Meta_getLocalDecl(x_2, x_14, x_15, x_16, x_17, x_27);
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
lean_dec(x_17);
lean_dec(x_15);
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
x_39 = l_Lean_Expr_getAppNumArgsAux(x_37, x_38);
x_40 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1, x_11, x_12, x_13, x_20, x_26, x_37, x_41, x_43, x_14, x_15, x_16, x_17, x_36);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_array_get_size(x_1);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_21, x_2, x_1);
lean_inc(x_3);
x_23 = l_Lean_mkFVar(x_3);
x_24 = lean_box(x_11);
lean_inc(x_4);
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 18, 13);
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
x_26 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_4, x_25, x_15, x_16, x_17, x_18, x_19);
return x_26;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1() {
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("after revert&intro\n", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
x_24 = l_Lean_Meta_revert(x_4, x_22, x_23, x_14, x_15, x_16, x_17, x_18);
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
x_41 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1;
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5(x_34, x_1, x_20, x_2, x_41);
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
x_47 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2(x_34, x_2, x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27, x_43, x_46, x_14, x_15, x_16, x_17, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_40);
x_48 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_48, 0, x_40);
x_49 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3;
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
x_56 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2(x_34, x_2, x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27, x_43, x_54, x_14, x_15, x_16, x_17, x_55);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' does not support dependent elimination, but conclusion depends on major premise", 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_18, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_16, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_14, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_7, 6);
lean_inc(x_25);
x_26 = l_List_redLength___rarg(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___rarg(x_25, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_30, x_31, x_28, x_13, x_14, x_15, x_16, x_24);
lean_dec(x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_38 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_st_ref_get(x_16, x_37);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_14, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = l_Lean_exprDependsOn(x_36, x_2, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_ctor_set(x_57, 0, x_63);
x_64 = lean_st_ref_set(x_14, x_57, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_unbox(x_62);
lean_dec(x_62);
x_39 = x_66;
x_40 = x_65;
goto block_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_67 = lean_ctor_get(x_57, 0);
x_68 = lean_ctor_get(x_57, 1);
x_69 = lean_ctor_get(x_57, 2);
x_70 = lean_ctor_get(x_57, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_57);
x_71 = l_Lean_exprDependsOn(x_36, x_2, x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_70);
x_75 = lean_st_ref_set(x_14, x_74, x_58);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_unbox(x_72);
lean_dec(x_72);
x_39 = x_77;
x_40 = x_76;
goto block_53;
}
}
else
{
uint8_t x_78; 
lean_dec(x_36);
x_78 = 0;
x_39 = x_78;
x_40 = x_37;
goto block_53;
}
block_53:
{
if (x_39 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_33, x_31, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_18, x_38, x_5, x_41, x_13, x_14, x_15, x_16, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_3);
x_44 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_47, x_13, x_14, x_15, x_16, x_40);
lean_dec(x_16);
lean_dec(x_14);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_33);
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
x_79 = !lean_is_exclusive(x_35);
if (x_79 == 0)
{
return x_35;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_35, 0);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_35);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
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
x_83 = !lean_is_exclusive(x_32);
if (x_83 == 0)
{
return x_32;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_32, 0);
x_85 = lean_ctor_get(x_32, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_32);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
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
x_87 = !lean_is_exclusive(x_19);
if (x_87 == 0)
{
return x_19;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_19, 0);
x_89 = lean_ctor_get(x_19, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_19);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
case 1:
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_12);
lean_dec(x_10);
x_91 = lean_ctor_get(x_7, 5);
lean_inc(x_91);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_92 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_91, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_st_ref_get(x_16, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_14, x_95);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get(x_7, 6);
lean_inc(x_98);
x_99 = l_List_redLength___rarg(x_98);
x_100 = lean_mk_empty_array_with_capacity(x_99);
lean_dec(x_99);
x_101 = l_List_toArrayAux___rarg(x_98, x_100);
x_102 = lean_array_get_size(x_101);
x_103 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_104 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_105 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_103, x_104, x_101, x_13, x_14, x_15, x_16, x_97);
lean_dec(x_11);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_1);
x_108 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_111 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_127 = lean_st_ref_get(x_16, x_110);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_14, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = l_Lean_exprDependsOn(x_109, x_2, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_ctor_set(x_130, 0, x_136);
x_137 = lean_st_ref_set(x_14, x_130, x_131);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_unbox(x_135);
lean_dec(x_135);
x_112 = x_139;
x_113 = x_138;
goto block_126;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_140 = lean_ctor_get(x_130, 0);
x_141 = lean_ctor_get(x_130, 1);
x_142 = lean_ctor_get(x_130, 2);
x_143 = lean_ctor_get(x_130, 3);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_130);
x_144 = l_Lean_exprDependsOn(x_109, x_2, x_140);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
lean_ctor_set(x_147, 2, x_142);
lean_ctor_set(x_147, 3, x_143);
x_148 = lean_st_ref_set(x_14, x_147, x_131);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_unbox(x_145);
lean_dec(x_145);
x_112 = x_150;
x_113 = x_149;
goto block_126;
}
}
else
{
uint8_t x_151; 
lean_dec(x_109);
x_151 = 0;
x_112 = x_151;
x_113 = x_110;
goto block_126;
}
block_126:
{
if (x_112 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_box(0);
x_115 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_106, x_104, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_91, x_111, x_5, x_114, x_13, x_14, x_15, x_16, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_116, 0, x_3);
x_117 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_120, x_13, x_14, x_15, x_16, x_113);
lean_dec(x_16);
lean_dec(x_14);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_106);
lean_dec(x_91);
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
x_152 = !lean_is_exclusive(x_108);
if (x_152 == 0)
{
return x_108;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_108, 0);
x_154 = lean_ctor_get(x_108, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_108);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_91);
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
x_156 = !lean_is_exclusive(x_105);
if (x_156 == 0)
{
return x_105;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_105, 0);
x_158 = lean_ctor_get(x_105, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_105);
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
lean_dec(x_91);
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
x_160 = !lean_is_exclusive(x_92);
if (x_160 == 0)
{
return x_92;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_92, 0);
x_162 = lean_ctor_get(x_92, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_92);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
case 2:
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_12);
lean_dec(x_10);
x_164 = lean_ctor_get(x_7, 5);
lean_inc(x_164);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_165 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_164, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; size_t x_176; size_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_st_ref_get(x_16, x_166);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_ref_get(x_14, x_168);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_ctor_get(x_7, 6);
lean_inc(x_171);
x_172 = l_List_redLength___rarg(x_171);
x_173 = lean_mk_empty_array_with_capacity(x_172);
lean_dec(x_172);
x_174 = l_List_toArrayAux___rarg(x_171, x_173);
x_175 = lean_array_get_size(x_174);
x_176 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_177 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_178 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_176, x_177, x_174, x_13, x_14, x_15, x_16, x_170);
lean_dec(x_11);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_1);
x_181 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_184 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_st_ref_get(x_16, x_183);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_st_ref_take(x_14, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_206 = lean_ctor_get(x_203, 0);
x_207 = l_Lean_exprDependsOn(x_182, x_2, x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_ctor_set(x_203, 0, x_209);
x_210 = lean_st_ref_set(x_14, x_203, x_204);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_unbox(x_208);
lean_dec(x_208);
x_185 = x_212;
x_186 = x_211;
goto block_199;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_213 = lean_ctor_get(x_203, 0);
x_214 = lean_ctor_get(x_203, 1);
x_215 = lean_ctor_get(x_203, 2);
x_216 = lean_ctor_get(x_203, 3);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_203);
x_217 = l_Lean_exprDependsOn(x_182, x_2, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_214);
lean_ctor_set(x_220, 2, x_215);
lean_ctor_set(x_220, 3, x_216);
x_221 = lean_st_ref_set(x_14, x_220, x_204);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_unbox(x_218);
lean_dec(x_218);
x_185 = x_223;
x_186 = x_222;
goto block_199;
}
}
else
{
uint8_t x_224; 
lean_dec(x_182);
x_224 = 0;
x_185 = x_224;
x_186 = x_183;
goto block_199;
}
block_199:
{
if (x_185 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_box(0);
x_188 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_179, x_177, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_164, x_184, x_5, x_187, x_13, x_14, x_15, x_16, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_179);
lean_dec(x_164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_189 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_189, 0, x_3);
x_190 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_191 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_193 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_193, x_13, x_14, x_15, x_16, x_186);
lean_dec(x_16);
lean_dec(x_14);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
return x_194;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_194);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_179);
lean_dec(x_164);
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
x_225 = !lean_is_exclusive(x_181);
if (x_225 == 0)
{
return x_181;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_181, 0);
x_227 = lean_ctor_get(x_181, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_181);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_164);
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
x_229 = !lean_is_exclusive(x_178);
if (x_229 == 0)
{
return x_178;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_178, 0);
x_231 = lean_ctor_get(x_178, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_178);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_164);
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
x_233 = !lean_is_exclusive(x_165);
if (x_233 == 0)
{
return x_165;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_165, 0);
x_235 = lean_ctor_get(x_165, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_165);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
case 3:
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_12);
lean_dec(x_10);
x_237 = lean_ctor_get(x_7, 5);
lean_inc(x_237);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_238 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_237, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; size_t x_249; size_t x_250; lean_object* x_251; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_st_ref_get(x_16, x_239);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_st_ref_get(x_14, x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_ctor_get(x_7, 6);
lean_inc(x_244);
x_245 = l_List_redLength___rarg(x_244);
x_246 = lean_mk_empty_array_with_capacity(x_245);
lean_dec(x_245);
x_247 = l_List_toArrayAux___rarg(x_244, x_246);
x_248 = lean_array_get_size(x_247);
x_249 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_250 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_251 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_249, x_250, x_247, x_13, x_14, x_15, x_16, x_243);
lean_dec(x_11);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_1);
x_254 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_257 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_273 = lean_st_ref_get(x_16, x_256);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_st_ref_take(x_14, x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = !lean_is_exclusive(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_279 = lean_ctor_get(x_276, 0);
x_280 = l_Lean_exprDependsOn(x_255, x_2, x_279);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
lean_ctor_set(x_276, 0, x_282);
x_283 = lean_st_ref_set(x_14, x_276, x_277);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_unbox(x_281);
lean_dec(x_281);
x_258 = x_285;
x_259 = x_284;
goto block_272;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_286 = lean_ctor_get(x_276, 0);
x_287 = lean_ctor_get(x_276, 1);
x_288 = lean_ctor_get(x_276, 2);
x_289 = lean_ctor_get(x_276, 3);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_276);
x_290 = l_Lean_exprDependsOn(x_255, x_2, x_286);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_287);
lean_ctor_set(x_293, 2, x_288);
lean_ctor_set(x_293, 3, x_289);
x_294 = lean_st_ref_set(x_14, x_293, x_277);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_unbox(x_291);
lean_dec(x_291);
x_258 = x_296;
x_259 = x_295;
goto block_272;
}
}
else
{
uint8_t x_297; 
lean_dec(x_255);
x_297 = 0;
x_258 = x_297;
x_259 = x_256;
goto block_272;
}
block_272:
{
if (x_258 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_box(0);
x_261 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_252, x_250, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_237, x_257, x_5, x_260, x_13, x_14, x_15, x_16, x_259);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_dec(x_252);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_262 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_262, 0, x_3);
x_263 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_264 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_266 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_266, x_13, x_14, x_15, x_16, x_259);
lean_dec(x_16);
lean_dec(x_14);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
return x_267;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_267);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_252);
lean_dec(x_237);
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
x_298 = !lean_is_exclusive(x_254);
if (x_298 == 0)
{
return x_254;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_254, 0);
x_300 = lean_ctor_get(x_254, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_254);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_237);
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
x_302 = !lean_is_exclusive(x_251);
if (x_302 == 0)
{
return x_251;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_251, 0);
x_304 = lean_ctor_get(x_251, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_251);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_237);
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
x_306 = !lean_is_exclusive(x_238);
if (x_306 == 0)
{
return x_238;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_238, 0);
x_308 = lean_ctor_get(x_238, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_238);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
case 4:
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_12);
lean_dec(x_10);
x_310 = lean_ctor_get(x_7, 5);
lean_inc(x_310);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_311 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_310, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; size_t x_322; size_t x_323; lean_object* x_324; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_313 = lean_st_ref_get(x_16, x_312);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_st_ref_get(x_14, x_314);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_ctor_get(x_7, 6);
lean_inc(x_317);
x_318 = l_List_redLength___rarg(x_317);
x_319 = lean_mk_empty_array_with_capacity(x_318);
lean_dec(x_318);
x_320 = l_List_toArrayAux___rarg(x_317, x_319);
x_321 = lean_array_get_size(x_320);
x_322 = lean_usize_of_nat(x_321);
lean_dec(x_321);
x_323 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_324 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_322, x_323, x_320, x_13, x_14, x_15, x_16, x_316);
lean_dec(x_11);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
lean_inc(x_1);
x_327 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_326);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_330 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_346 = lean_st_ref_get(x_16, x_329);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_348 = lean_st_ref_take(x_14, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = !lean_is_exclusive(x_349);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_352 = lean_ctor_get(x_349, 0);
x_353 = l_Lean_exprDependsOn(x_328, x_2, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_ctor_set(x_349, 0, x_355);
x_356 = lean_st_ref_set(x_14, x_349, x_350);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
x_358 = lean_unbox(x_354);
lean_dec(x_354);
x_331 = x_358;
x_332 = x_357;
goto block_345;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_359 = lean_ctor_get(x_349, 0);
x_360 = lean_ctor_get(x_349, 1);
x_361 = lean_ctor_get(x_349, 2);
x_362 = lean_ctor_get(x_349, 3);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_349);
x_363 = l_Lean_exprDependsOn(x_328, x_2, x_359);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_360);
lean_ctor_set(x_366, 2, x_361);
lean_ctor_set(x_366, 3, x_362);
x_367 = lean_st_ref_set(x_14, x_366, x_350);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_369 = lean_unbox(x_364);
lean_dec(x_364);
x_331 = x_369;
x_332 = x_368;
goto block_345;
}
}
else
{
uint8_t x_370; 
lean_dec(x_328);
x_370 = 0;
x_331 = x_370;
x_332 = x_329;
goto block_345;
}
block_345:
{
if (x_331 == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_box(0);
x_334 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_325, x_323, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_310, x_330, x_5, x_333, x_13, x_14, x_15, x_16, x_332);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_325);
lean_dec(x_310);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_335 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_335, 0, x_3);
x_336 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_339 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_339, x_13, x_14, x_15, x_16, x_332);
lean_dec(x_16);
lean_dec(x_14);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
return x_340;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_340);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_325);
lean_dec(x_310);
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
x_371 = !lean_is_exclusive(x_327);
if (x_371 == 0)
{
return x_327;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_327, 0);
x_373 = lean_ctor_get(x_327, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_327);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_310);
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
x_375 = !lean_is_exclusive(x_324);
if (x_375 == 0)
{
return x_324;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_324, 0);
x_377 = lean_ctor_get(x_324, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_324);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_310);
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
x_379 = !lean_is_exclusive(x_311);
if (x_379 == 0)
{
return x_311;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_311, 0);
x_381 = lean_ctor_get(x_311, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_311);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
case 5:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_10, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_10, 1);
lean_inc(x_384);
lean_dec(x_10);
x_385 = lean_array_set(x_11, x_12, x_384);
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_nat_sub(x_12, x_386);
lean_dec(x_12);
x_10 = x_383;
x_11 = x_385;
x_12 = x_387;
goto _start;
}
case 6:
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_12);
lean_dec(x_10);
x_389 = lean_ctor_get(x_7, 5);
lean_inc(x_389);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_390 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_389, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; size_t x_401; size_t x_402; lean_object* x_403; 
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_st_ref_get(x_16, x_391);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
lean_dec(x_392);
x_394 = lean_st_ref_get(x_14, x_393);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_ctor_get(x_7, 6);
lean_inc(x_396);
x_397 = l_List_redLength___rarg(x_396);
x_398 = lean_mk_empty_array_with_capacity(x_397);
lean_dec(x_397);
x_399 = l_List_toArrayAux___rarg(x_396, x_398);
x_400 = lean_array_get_size(x_399);
x_401 = lean_usize_of_nat(x_400);
lean_dec(x_400);
x_402 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_403 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_401, x_402, x_399, x_13, x_14, x_15, x_16, x_395);
lean_dec(x_11);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
lean_inc(x_1);
x_406 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_405);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_409 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_425 = lean_st_ref_get(x_16, x_408);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_st_ref_take(x_14, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = !lean_is_exclusive(x_428);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_431 = lean_ctor_get(x_428, 0);
x_432 = l_Lean_exprDependsOn(x_407, x_2, x_431);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
lean_ctor_set(x_428, 0, x_434);
x_435 = lean_st_ref_set(x_14, x_428, x_429);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = lean_unbox(x_433);
lean_dec(x_433);
x_410 = x_437;
x_411 = x_436;
goto block_424;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_438 = lean_ctor_get(x_428, 0);
x_439 = lean_ctor_get(x_428, 1);
x_440 = lean_ctor_get(x_428, 2);
x_441 = lean_ctor_get(x_428, 3);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_428);
x_442 = l_Lean_exprDependsOn(x_407, x_2, x_438);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
x_446 = lean_st_ref_set(x_14, x_445, x_429);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_unbox(x_443);
lean_dec(x_443);
x_410 = x_448;
x_411 = x_447;
goto block_424;
}
}
else
{
uint8_t x_449; 
lean_dec(x_407);
x_449 = 0;
x_410 = x_449;
x_411 = x_408;
goto block_424;
}
block_424:
{
if (x_410 == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_box(0);
x_413 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_404, x_402, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_389, x_409, x_5, x_412, x_13, x_14, x_15, x_16, x_411);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
lean_dec(x_404);
lean_dec(x_389);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_414 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_414, 0, x_3);
x_415 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_416 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_414);
x_417 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_418, x_13, x_14, x_15, x_16, x_411);
lean_dec(x_16);
lean_dec(x_14);
x_420 = !lean_is_exclusive(x_419);
if (x_420 == 0)
{
return x_419;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_419, 0);
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_419);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_404);
lean_dec(x_389);
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
x_450 = !lean_is_exclusive(x_406);
if (x_450 == 0)
{
return x_406;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_406, 0);
x_452 = lean_ctor_get(x_406, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_406);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_389);
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
x_454 = !lean_is_exclusive(x_403);
if (x_454 == 0)
{
return x_403;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_403, 0);
x_456 = lean_ctor_get(x_403, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_403);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_389);
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
x_458 = !lean_is_exclusive(x_390);
if (x_458 == 0)
{
return x_390;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_390, 0);
x_460 = lean_ctor_get(x_390, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_390);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
case 7:
{
lean_object* x_462; lean_object* x_463; 
lean_dec(x_12);
lean_dec(x_10);
x_462 = lean_ctor_get(x_7, 5);
lean_inc(x_462);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_463 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_462, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; size_t x_474; size_t x_475; lean_object* x_476; 
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
x_465 = lean_st_ref_get(x_16, x_464);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
lean_dec(x_465);
x_467 = lean_st_ref_get(x_14, x_466);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
lean_dec(x_467);
x_469 = lean_ctor_get(x_7, 6);
lean_inc(x_469);
x_470 = l_List_redLength___rarg(x_469);
x_471 = lean_mk_empty_array_with_capacity(x_470);
lean_dec(x_470);
x_472 = l_List_toArrayAux___rarg(x_469, x_471);
x_473 = lean_array_get_size(x_472);
x_474 = lean_usize_of_nat(x_473);
lean_dec(x_473);
x_475 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_476 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_474, x_475, x_472, x_13, x_14, x_15, x_16, x_468);
lean_dec(x_11);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
lean_inc(x_1);
x_479 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_478);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; uint8_t x_482; uint8_t x_483; lean_object* x_484; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_482 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_498 = lean_st_ref_get(x_16, x_481);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_500 = lean_st_ref_take(x_14, x_499);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = !lean_is_exclusive(x_501);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
x_504 = lean_ctor_get(x_501, 0);
x_505 = l_Lean_exprDependsOn(x_480, x_2, x_504);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
lean_ctor_set(x_501, 0, x_507);
x_508 = lean_st_ref_set(x_14, x_501, x_502);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_unbox(x_506);
lean_dec(x_506);
x_483 = x_510;
x_484 = x_509;
goto block_497;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_511 = lean_ctor_get(x_501, 0);
x_512 = lean_ctor_get(x_501, 1);
x_513 = lean_ctor_get(x_501, 2);
x_514 = lean_ctor_get(x_501, 3);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_501);
x_515 = l_Lean_exprDependsOn(x_480, x_2, x_511);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_512);
lean_ctor_set(x_518, 2, x_513);
lean_ctor_set(x_518, 3, x_514);
x_519 = lean_st_ref_set(x_14, x_518, x_502);
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_unbox(x_516);
lean_dec(x_516);
x_483 = x_521;
x_484 = x_520;
goto block_497;
}
}
else
{
uint8_t x_522; 
lean_dec(x_480);
x_522 = 0;
x_483 = x_522;
x_484 = x_481;
goto block_497;
}
block_497:
{
if (x_483 == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_box(0);
x_486 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_477, x_475, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_462, x_482, x_5, x_485, x_13, x_14, x_15, x_16, x_484);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
lean_dec(x_477);
lean_dec(x_462);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_487 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_487, 0, x_3);
x_488 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_487);
x_490 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_491 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_491, x_13, x_14, x_15, x_16, x_484);
lean_dec(x_16);
lean_dec(x_14);
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
return x_492;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_492, 0);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_492);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
}
else
{
uint8_t x_523; 
lean_dec(x_477);
lean_dec(x_462);
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
x_523 = !lean_is_exclusive(x_479);
if (x_523 == 0)
{
return x_479;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_479, 0);
x_525 = lean_ctor_get(x_479, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_479);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_462);
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
x_527 = !lean_is_exclusive(x_476);
if (x_527 == 0)
{
return x_476;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_476, 0);
x_529 = lean_ctor_get(x_476, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_476);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_462);
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
x_531 = !lean_is_exclusive(x_463);
if (x_531 == 0)
{
return x_463;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_463, 0);
x_533 = lean_ctor_get(x_463, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_463);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
case 8:
{
lean_object* x_535; lean_object* x_536; 
lean_dec(x_12);
lean_dec(x_10);
x_535 = lean_ctor_get(x_7, 5);
lean_inc(x_535);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_536 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_535, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; size_t x_547; size_t x_548; lean_object* x_549; 
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
x_538 = lean_st_ref_get(x_16, x_537);
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
lean_dec(x_538);
x_540 = lean_st_ref_get(x_14, x_539);
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_ctor_get(x_7, 6);
lean_inc(x_542);
x_543 = l_List_redLength___rarg(x_542);
x_544 = lean_mk_empty_array_with_capacity(x_543);
lean_dec(x_543);
x_545 = l_List_toArrayAux___rarg(x_542, x_544);
x_546 = lean_array_get_size(x_545);
x_547 = lean_usize_of_nat(x_546);
lean_dec(x_546);
x_548 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_549 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_547, x_548, x_545, x_13, x_14, x_15, x_16, x_541);
lean_dec(x_11);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
lean_inc(x_1);
x_552 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_551);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; uint8_t x_555; uint8_t x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_555 == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_571 = lean_st_ref_get(x_16, x_554);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
lean_dec(x_571);
x_573 = lean_st_ref_take(x_14, x_572);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = !lean_is_exclusive(x_574);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_577 = lean_ctor_get(x_574, 0);
x_578 = l_Lean_exprDependsOn(x_553, x_2, x_577);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
lean_dec(x_578);
lean_ctor_set(x_574, 0, x_580);
x_581 = lean_st_ref_set(x_14, x_574, x_575);
x_582 = lean_ctor_get(x_581, 1);
lean_inc(x_582);
lean_dec(x_581);
x_583 = lean_unbox(x_579);
lean_dec(x_579);
x_556 = x_583;
x_557 = x_582;
goto block_570;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_584 = lean_ctor_get(x_574, 0);
x_585 = lean_ctor_get(x_574, 1);
x_586 = lean_ctor_get(x_574, 2);
x_587 = lean_ctor_get(x_574, 3);
lean_inc(x_587);
lean_inc(x_586);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_574);
x_588 = l_Lean_exprDependsOn(x_553, x_2, x_584);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_591 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_585);
lean_ctor_set(x_591, 2, x_586);
lean_ctor_set(x_591, 3, x_587);
x_592 = lean_st_ref_set(x_14, x_591, x_575);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec(x_592);
x_594 = lean_unbox(x_589);
lean_dec(x_589);
x_556 = x_594;
x_557 = x_593;
goto block_570;
}
}
else
{
uint8_t x_595; 
lean_dec(x_553);
x_595 = 0;
x_556 = x_595;
x_557 = x_554;
goto block_570;
}
block_570:
{
if (x_556 == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_box(0);
x_559 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_550, x_548, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_535, x_555, x_5, x_558, x_13, x_14, x_15, x_16, x_557);
return x_559;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; 
lean_dec(x_550);
lean_dec(x_535);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_560 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_560, 0, x_3);
x_561 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_562 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_560);
x_563 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_564 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
x_565 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_564, x_13, x_14, x_15, x_16, x_557);
lean_dec(x_16);
lean_dec(x_14);
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
return x_565;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_565, 0);
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_565);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_550);
lean_dec(x_535);
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
x_596 = !lean_is_exclusive(x_552);
if (x_596 == 0)
{
return x_552;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_552, 0);
x_598 = lean_ctor_get(x_552, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_552);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
else
{
uint8_t x_600; 
lean_dec(x_535);
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
x_600 = !lean_is_exclusive(x_549);
if (x_600 == 0)
{
return x_549;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_549, 0);
x_602 = lean_ctor_get(x_549, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_549);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
else
{
uint8_t x_604; 
lean_dec(x_535);
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
x_604 = !lean_is_exclusive(x_536);
if (x_604 == 0)
{
return x_536;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_536, 0);
x_606 = lean_ctor_get(x_536, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_536);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
}
}
case 9:
{
lean_object* x_608; lean_object* x_609; 
lean_dec(x_12);
lean_dec(x_10);
x_608 = lean_ctor_get(x_7, 5);
lean_inc(x_608);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_609 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_608, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; size_t x_620; size_t x_621; lean_object* x_622; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = lean_st_ref_get(x_16, x_610);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec(x_611);
x_613 = lean_st_ref_get(x_14, x_612);
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_ctor_get(x_7, 6);
lean_inc(x_615);
x_616 = l_List_redLength___rarg(x_615);
x_617 = lean_mk_empty_array_with_capacity(x_616);
lean_dec(x_616);
x_618 = l_List_toArrayAux___rarg(x_615, x_617);
x_619 = lean_array_get_size(x_618);
x_620 = lean_usize_of_nat(x_619);
lean_dec(x_619);
x_621 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_622 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_620, x_621, x_618, x_13, x_14, x_15, x_16, x_614);
lean_dec(x_11);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
lean_inc(x_1);
x_625 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_624);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; uint8_t x_628; uint8_t x_629; lean_object* x_630; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
lean_dec(x_625);
x_628 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_628 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_644 = lean_st_ref_get(x_16, x_627);
x_645 = lean_ctor_get(x_644, 1);
lean_inc(x_645);
lean_dec(x_644);
x_646 = lean_st_ref_take(x_14, x_645);
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
x_649 = !lean_is_exclusive(x_647);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; 
x_650 = lean_ctor_get(x_647, 0);
x_651 = l_Lean_exprDependsOn(x_626, x_2, x_650);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
lean_ctor_set(x_647, 0, x_653);
x_654 = lean_st_ref_set(x_14, x_647, x_648);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
lean_dec(x_654);
x_656 = lean_unbox(x_652);
lean_dec(x_652);
x_629 = x_656;
x_630 = x_655;
goto block_643;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_657 = lean_ctor_get(x_647, 0);
x_658 = lean_ctor_get(x_647, 1);
x_659 = lean_ctor_get(x_647, 2);
x_660 = lean_ctor_get(x_647, 3);
lean_inc(x_660);
lean_inc(x_659);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_647);
x_661 = l_Lean_exprDependsOn(x_626, x_2, x_657);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_658);
lean_ctor_set(x_664, 2, x_659);
lean_ctor_set(x_664, 3, x_660);
x_665 = lean_st_ref_set(x_14, x_664, x_648);
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
lean_dec(x_665);
x_667 = lean_unbox(x_662);
lean_dec(x_662);
x_629 = x_667;
x_630 = x_666;
goto block_643;
}
}
else
{
uint8_t x_668; 
lean_dec(x_626);
x_668 = 0;
x_629 = x_668;
x_630 = x_627;
goto block_643;
}
block_643:
{
if (x_629 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_box(0);
x_632 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_623, x_621, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_608, x_628, x_5, x_631, x_13, x_14, x_15, x_16, x_630);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
lean_dec(x_623);
lean_dec(x_608);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_633 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_633, 0, x_3);
x_634 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_635 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_633);
x_636 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_637 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
x_638 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_637, x_13, x_14, x_15, x_16, x_630);
lean_dec(x_16);
lean_dec(x_14);
x_639 = !lean_is_exclusive(x_638);
if (x_639 == 0)
{
return x_638;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_638, 0);
x_641 = lean_ctor_get(x_638, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_638);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
}
else
{
uint8_t x_669; 
lean_dec(x_623);
lean_dec(x_608);
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
x_669 = !lean_is_exclusive(x_625);
if (x_669 == 0)
{
return x_625;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_625, 0);
x_671 = lean_ctor_get(x_625, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_625);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
else
{
uint8_t x_673; 
lean_dec(x_608);
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
x_673 = !lean_is_exclusive(x_622);
if (x_673 == 0)
{
return x_622;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_674 = lean_ctor_get(x_622, 0);
x_675 = lean_ctor_get(x_622, 1);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_622);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
}
else
{
uint8_t x_677; 
lean_dec(x_608);
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
x_677 = !lean_is_exclusive(x_609);
if (x_677 == 0)
{
return x_609;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_609, 0);
x_679 = lean_ctor_get(x_609, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_609);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
case 10:
{
lean_object* x_681; lean_object* x_682; 
lean_dec(x_12);
lean_dec(x_10);
x_681 = lean_ctor_get(x_7, 5);
lean_inc(x_681);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_682 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_681, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; size_t x_693; size_t x_694; lean_object* x_695; 
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
lean_dec(x_682);
x_684 = lean_st_ref_get(x_16, x_683);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_686 = lean_st_ref_get(x_14, x_685);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
x_688 = lean_ctor_get(x_7, 6);
lean_inc(x_688);
x_689 = l_List_redLength___rarg(x_688);
x_690 = lean_mk_empty_array_with_capacity(x_689);
lean_dec(x_689);
x_691 = l_List_toArrayAux___rarg(x_688, x_690);
x_692 = lean_array_get_size(x_691);
x_693 = lean_usize_of_nat(x_692);
lean_dec(x_692);
x_694 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_695 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_693, x_694, x_691, x_13, x_14, x_15, x_16, x_687);
lean_dec(x_11);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
lean_inc(x_1);
x_698 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_697);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; lean_object* x_700; uint8_t x_701; uint8_t x_702; lean_object* x_703; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
x_701 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_701 == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; 
x_717 = lean_st_ref_get(x_16, x_700);
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec(x_717);
x_719 = lean_st_ref_take(x_14, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = !lean_is_exclusive(x_720);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_723 = lean_ctor_get(x_720, 0);
x_724 = l_Lean_exprDependsOn(x_699, x_2, x_723);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
lean_ctor_set(x_720, 0, x_726);
x_727 = lean_st_ref_set(x_14, x_720, x_721);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
lean_dec(x_727);
x_729 = lean_unbox(x_725);
lean_dec(x_725);
x_702 = x_729;
x_703 = x_728;
goto block_716;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; 
x_730 = lean_ctor_get(x_720, 0);
x_731 = lean_ctor_get(x_720, 1);
x_732 = lean_ctor_get(x_720, 2);
x_733 = lean_ctor_get(x_720, 3);
lean_inc(x_733);
lean_inc(x_732);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_720);
x_734 = l_Lean_exprDependsOn(x_699, x_2, x_730);
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_731);
lean_ctor_set(x_737, 2, x_732);
lean_ctor_set(x_737, 3, x_733);
x_738 = lean_st_ref_set(x_14, x_737, x_721);
x_739 = lean_ctor_get(x_738, 1);
lean_inc(x_739);
lean_dec(x_738);
x_740 = lean_unbox(x_735);
lean_dec(x_735);
x_702 = x_740;
x_703 = x_739;
goto block_716;
}
}
else
{
uint8_t x_741; 
lean_dec(x_699);
x_741 = 0;
x_702 = x_741;
x_703 = x_700;
goto block_716;
}
block_716:
{
if (x_702 == 0)
{
lean_object* x_704; lean_object* x_705; 
x_704 = lean_box(0);
x_705 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_696, x_694, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_681, x_701, x_5, x_704, x_13, x_14, x_15, x_16, x_703);
return x_705;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; 
lean_dec(x_696);
lean_dec(x_681);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_706 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_706, 0, x_3);
x_707 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_708 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_710 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
x_711 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_710, x_13, x_14, x_15, x_16, x_703);
lean_dec(x_16);
lean_dec(x_14);
x_712 = !lean_is_exclusive(x_711);
if (x_712 == 0)
{
return x_711;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_711, 0);
x_714 = lean_ctor_get(x_711, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_711);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
}
else
{
uint8_t x_742; 
lean_dec(x_696);
lean_dec(x_681);
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
x_742 = !lean_is_exclusive(x_698);
if (x_742 == 0)
{
return x_698;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_698, 0);
x_744 = lean_ctor_get(x_698, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_698);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
}
else
{
uint8_t x_746; 
lean_dec(x_681);
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
x_746 = !lean_is_exclusive(x_695);
if (x_746 == 0)
{
return x_695;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_747 = lean_ctor_get(x_695, 0);
x_748 = lean_ctor_get(x_695, 1);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_695);
x_749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_748);
return x_749;
}
}
}
else
{
uint8_t x_750; 
lean_dec(x_681);
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
x_750 = !lean_is_exclusive(x_682);
if (x_750 == 0)
{
return x_682;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_682, 0);
x_752 = lean_ctor_get(x_682, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_682);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
return x_753;
}
}
}
default: 
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_12);
lean_dec(x_10);
x_754 = lean_ctor_get(x_7, 5);
lean_inc(x_754);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_755 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_754, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; size_t x_766; size_t x_767; lean_object* x_768; 
x_756 = lean_ctor_get(x_755, 1);
lean_inc(x_756);
lean_dec(x_755);
x_757 = lean_st_ref_get(x_16, x_756);
x_758 = lean_ctor_get(x_757, 1);
lean_inc(x_758);
lean_dec(x_757);
x_759 = lean_st_ref_get(x_14, x_758);
x_760 = lean_ctor_get(x_759, 1);
lean_inc(x_760);
lean_dec(x_759);
x_761 = lean_ctor_get(x_7, 6);
lean_inc(x_761);
x_762 = l_List_redLength___rarg(x_761);
x_763 = lean_mk_empty_array_with_capacity(x_762);
lean_dec(x_762);
x_764 = l_List_toArrayAux___rarg(x_761, x_763);
x_765 = lean_array_get_size(x_764);
x_766 = lean_usize_of_nat(x_765);
lean_dec(x_765);
x_767 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_768 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_6, x_7, x_9, x_11, x_766, x_767, x_764, x_13, x_14, x_15, x_16, x_760);
lean_dec(x_11);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
lean_inc(x_1);
x_771 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; uint8_t x_774; uint8_t x_775; lean_object* x_776; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_774 == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_790 = lean_st_ref_get(x_16, x_773);
x_791 = lean_ctor_get(x_790, 1);
lean_inc(x_791);
lean_dec(x_790);
x_792 = lean_st_ref_take(x_14, x_791);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = !lean_is_exclusive(x_793);
if (x_795 == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
x_796 = lean_ctor_get(x_793, 0);
x_797 = l_Lean_exprDependsOn(x_772, x_2, x_796);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
lean_ctor_set(x_793, 0, x_799);
x_800 = lean_st_ref_set(x_14, x_793, x_794);
x_801 = lean_ctor_get(x_800, 1);
lean_inc(x_801);
lean_dec(x_800);
x_802 = lean_unbox(x_798);
lean_dec(x_798);
x_775 = x_802;
x_776 = x_801;
goto block_789;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; 
x_803 = lean_ctor_get(x_793, 0);
x_804 = lean_ctor_get(x_793, 1);
x_805 = lean_ctor_get(x_793, 2);
x_806 = lean_ctor_get(x_793, 3);
lean_inc(x_806);
lean_inc(x_805);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_793);
x_807 = l_Lean_exprDependsOn(x_772, x_2, x_803);
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_804);
lean_ctor_set(x_810, 2, x_805);
lean_ctor_set(x_810, 3, x_806);
x_811 = lean_st_ref_set(x_14, x_810, x_794);
x_812 = lean_ctor_get(x_811, 1);
lean_inc(x_812);
lean_dec(x_811);
x_813 = lean_unbox(x_808);
lean_dec(x_808);
x_775 = x_813;
x_776 = x_812;
goto block_789;
}
}
else
{
uint8_t x_814; 
lean_dec(x_772);
x_814 = 0;
x_775 = x_814;
x_776 = x_773;
goto block_789;
}
block_789:
{
if (x_775 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_box(0);
x_778 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_769, x_767, x_2, x_1, x_8, x_3, x_4, x_6, x_7, x_754, x_774, x_5, x_777, x_13, x_14, x_15, x_16, x_776);
return x_778;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; uint8_t x_785; 
lean_dec(x_769);
lean_dec(x_754);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_779 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_779, 0, x_3);
x_780 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6;
x_781 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_779);
x_782 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2;
x_783 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_783, 0, x_781);
lean_ctor_set(x_783, 1, x_782);
x_784 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_783, x_13, x_14, x_15, x_16, x_776);
lean_dec(x_16);
lean_dec(x_14);
x_785 = !lean_is_exclusive(x_784);
if (x_785 == 0)
{
return x_784;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_784, 0);
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_784);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
}
else
{
uint8_t x_815; 
lean_dec(x_769);
lean_dec(x_754);
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
x_815 = !lean_is_exclusive(x_771);
if (x_815 == 0)
{
return x_771;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_771, 0);
x_817 = lean_ctor_get(x_771, 1);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_771);
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
}
else
{
uint8_t x_819; 
lean_dec(x_754);
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
x_819 = !lean_is_exclusive(x_768);
if (x_819 == 0)
{
return x_768;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_768, 0);
x_821 = lean_ctor_get(x_768, 1);
lean_inc(x_821);
lean_inc(x_820);
lean_dec(x_768);
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
}
else
{
uint8_t x_823; 
lean_dec(x_754);
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
x_823 = !lean_is_exclusive(x_755);
if (x_823 == 0)
{
return x_755;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_824 = lean_ctor_get(x_755, 0);
x_825 = lean_ctor_get(x_755, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_755);
x_826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_Meta_getLocalDecl(x_2, x_7, x_8, x_9, x_10, x_14);
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
lean_dec(x_10);
lean_dec(x_8);
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
x_31 = l_Lean_Expr_getAppNumArgsAux(x_29, x_30);
x_32 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_29);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_12, x_20, x_23, x_29, x_29, x_33, x_35, x_7, x_8, x_9, x_10, x_28);
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
static lean_object* _init_l_Lean_Meta_induction___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initial\n", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_induction___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_induction___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_induction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_13, x_6, x_7, x_8, x_9, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Meta_induction___lambda__2___closed__2;
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
x_23 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_21, x_6, x_7, x_8, x_9, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Meta_induction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_induction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_induction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_induction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_induction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_induction___closed__2;
x_2 = l_Lean_Meta_induction___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_induction___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_induction___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_induction___closed__5;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__2), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_10);
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Meta_induction___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_List_foldlM___at_Lean_Meta_induction___spec__6___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___boxed(lean_object** _args) {
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
x_21 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___boxed(lean_object** _args) {
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
x_23 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object** _args) {
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
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2___boxed(lean_object** _args) {
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
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__2(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___boxed(lean_object** _args) {
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
x_21 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___boxed(lean_object** _args) {
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
x_18 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3288_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_induction___closed__5;
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
l_List_forM___at_Lean_Meta_induction___spec__1___closed__1 = _init_l_List_forM___at_Lean_Meta_induction___spec__1___closed__1();
lean_mark_persistent(l_List_forM___at_Lean_Meta_induction___spec__1___closed__1);
l_List_forM___at_Lean_Meta_induction___spec__1___closed__2 = _init_l_List_forM___at_Lean_Meta_induction___spec__1___closed__2();
lean_mark_persistent(l_List_forM___at_Lean_Meta_induction___spec__1___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__3);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__1___closed__4);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___lambda__2___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_induction___spec__4___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__7);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__7___closed__8);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___lambda__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__8___closed__2);
l_Lean_Meta_induction___lambda__2___closed__1 = _init_l_Lean_Meta_induction___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_induction___lambda__2___closed__1);
l_Lean_Meta_induction___lambda__2___closed__2 = _init_l_Lean_Meta_induction___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_induction___lambda__2___closed__2);
l_Lean_Meta_induction___closed__1 = _init_l_Lean_Meta_induction___closed__1();
lean_mark_persistent(l_Lean_Meta_induction___closed__1);
l_Lean_Meta_induction___closed__2 = _init_l_Lean_Meta_induction___closed__2();
lean_mark_persistent(l_Lean_Meta_induction___closed__2);
l_Lean_Meta_induction___closed__3 = _init_l_Lean_Meta_induction___closed__3();
lean_mark_persistent(l_Lean_Meta_induction___closed__3);
l_Lean_Meta_induction___closed__4 = _init_l_Lean_Meta_induction___closed__4();
lean_mark_persistent(l_Lean_Meta_induction___closed__4);
l_Lean_Meta_induction___closed__5 = _init_l_Lean_Meta_induction___closed__5();
lean_mark_persistent(l_Lean_Meta_induction___closed__5);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_3288_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
