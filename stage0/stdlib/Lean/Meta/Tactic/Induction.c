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
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_fields___default;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12;
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_InductionSubgoal_subst___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1;
lean_object* l_Lean_localDeclDependsOn___at_Lean_MVarId_clear___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7;
extern lean_object* l_Lean_instInhabitedLevel;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInductionSubgoal;
static lean_object* l_Lean_MVarId_induction___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_induction___lambda__2___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___boxed(lean_object**);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_Meta_Occurrences_contains___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AltVarNames_varNames___default;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object**);
static lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3;
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___boxed(lean_object**);
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1;
static lean_object* l_Lean_Meta_instInhabitedInductionSubgoal___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAltVarNames___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___boxed(lean_object**);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2;
static lean_object* l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_induction___closed__3;
static lean_object* l_Lean_MVarId_induction___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5;
static lean_object* l_Lean_MVarId_induction___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
static lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAltVarNames;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054_(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
LEAN_EXPORT uint8_t l_Lean_Meta_AltVarNames_explicit___default;
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
x_28 = l_Lean_Exception_isRuntime(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_21);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_30 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_31 = l_Lean_Meta_throwTacticEx___rarg(x_29, x_1, x_30, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_36 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_21);
lean_dec(x_26);
x_37 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_38 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_37, x_1, x_38, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
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
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = l_Lean_Exception_isRuntime(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
x_47 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_48 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_49 = l_Lean_Meta_throwTacticEx___rarg(x_47, x_1, x_48, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
x_56 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_57 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_58 = l_Lean_Meta_throwTacticEx___rarg(x_56, x_1, x_57, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_6);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
lean_dec(x_16);
x_64 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_65 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_66 = l_Lean_Meta_throwTacticEx___rarg(x_64, x_1, x_65, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_6);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
return x_13;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_13);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
lean_dec(x_3);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
lean_dec(x_11);
x_77 = lean_array_get_size(x_2);
x_78 = lean_nat_dec_lt(x_76, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_4);
lean_dec(x_2);
x_79 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_80 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_81 = l_Lean_Meta_throwTacticEx___rarg(x_79, x_1, x_80, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_array_fget(x_2, x_76);
lean_dec(x_76);
x_83 = l_Lean_Expr_app___override(x_4, x_82);
x_3 = x_75;
x_4 = x_83;
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
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_22 = l_Lean_instInhabitedFVarId;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
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
x_33 = l_Lean_instInhabitedFVarId;
x_34 = l___private_Init_Util_0__outOfBounds___rarg(x_33);
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
x_59 = l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_3, x_4, x_27, x_28, x_57, x_27, x_27, x_9);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_40; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_26 = l_Lean_Expr_headBeta(x_24);
x_40 = l_Lean_BinderInfo_isInstImplicit(x_25);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_27 = x_41;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = l_Array_isEmpty___rarg(x_12);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_27 = x_43;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
x_45 = l_Lean_Meta_synthInstance_x3f(x_26, x_44, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Name_append(x_16, x_23);
lean_inc(x_18);
x_49 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_48, x_18, x_19, x_20, x_21, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_50);
x_52 = l_Lean_Expr_app___override(x_5, x_50);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_53 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_50, x_18, x_19, x_20, x_21, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_9, x_56);
lean_dec(x_9);
x_58 = lean_nat_add(x_10, x_56);
lean_dec(x_10);
x_59 = l_Lean_Expr_mvarId_x21(x_50);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_InductionSubgoal_fields___default___closed__1;
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_array_push(x_11, x_62);
x_64 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_57, x_58, x_52, x_54, x_15, x_63, x_18, x_19, x_20, x_21, x_55);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_52);
lean_dec(x_50);
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
x_65 = !lean_is_exclusive(x_53);
if (x_65 == 0)
{
return x_53;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_53);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_16);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_dec(x_45);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
lean_dec(x_46);
lean_inc(x_70);
x_71 = l_Lean_Expr_app___override(x_5, x_70);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_72 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_70, x_18, x_19, x_20, x_21, x_69);
lean_dec(x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_9, x_75);
lean_dec(x_9);
x_77 = lean_nat_add(x_10, x_75);
lean_dec(x_10);
x_78 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_76, x_77, x_71, x_73, x_15, x_11, x_18, x_19, x_20, x_21, x_74);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_71);
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
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_72, 0);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_72);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
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
x_83 = !lean_is_exclusive(x_45);
if (x_83 == 0)
{
return x_45;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_45, 0);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_45);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
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
lean_object* x_87; lean_object* x_88; 
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
x_87 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__4;
x_88 = l_panic___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(x_87, x_18, x_19, x_20, x_21, x_22);
return x_88;
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
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_3, 3);
lean_inc(x_34);
x_35 = lean_nat_dec_lt(x_10, x_34);
lean_dec(x_34);
if (x_35 == 0)
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_12);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_37 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_36, x_1, x_37, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_17);
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
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_43, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_46 = lean_nat_dec_eq(x_10, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_inc(x_1);
x_47 = l_Lean_MVarId_getTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_nat_dec_le(x_9, x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_22, x_8, x_4, x_6, x_12, x_1, x_5, x_7, x_10, x_11, x_15, x_2, x_3, x_9, x_14, x_48, x_51, x_16, x_17, x_18, x_19, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_48);
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
x_53 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_54 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_55 = l_Lean_Meta_throwTacticEx___rarg(x_53, x_1, x_54, x_16, x_17, x_18, x_19, x_49);
lean_dec(x_19);
lean_dec(x_17);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_inc(x_22);
lean_inc(x_12);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_22);
x_65 = lean_array_get_size(x_6);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
lean_inc(x_5);
x_68 = l_Lean_Expr_app___override(x_12, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_69 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_22, x_5, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_10, x_72);
lean_dec(x_10);
x_74 = lean_nat_add(x_73, x_65);
lean_dec(x_65);
lean_dec(x_73);
x_75 = 1;
x_10 = x_74;
x_12 = x_68;
x_13 = x_70;
x_14 = x_75;
x_20 = x_71;
goto _start;
}
else
{
uint8_t x_77; 
lean_dec(x_68);
lean_dec(x_65);
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
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_65, x_65);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_inc(x_5);
x_82 = l_Lean_Expr_app___override(x_12, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_83 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_22, x_5, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_10, x_86);
lean_dec(x_10);
x_88 = lean_nat_add(x_87, x_65);
lean_dec(x_65);
lean_dec(x_87);
x_89 = 1;
x_10 = x_88;
x_12 = x_82;
x_13 = x_84;
x_14 = x_89;
x_20 = x_85;
goto _start;
}
else
{
uint8_t x_91; 
lean_dec(x_82);
lean_dec(x_65);
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
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
return x_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_83, 0);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_83);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
lean_dec(x_22);
lean_dec(x_12);
x_95 = 0;
x_96 = lean_usize_of_nat(x_65);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_97 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_6, x_95, x_96, x_64, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_5);
x_102 = l_Lean_Expr_app___override(x_100, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_103 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_101, x_5, x_16, x_17, x_18, x_19, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_10, x_106);
lean_dec(x_10);
x_108 = lean_nat_add(x_107, x_65);
lean_dec(x_65);
lean_dec(x_107);
x_109 = 1;
x_10 = x_108;
x_12 = x_102;
x_13 = x_104;
x_14 = x_109;
x_20 = x_105;
goto _start;
}
else
{
uint8_t x_111; 
lean_dec(x_102);
lean_dec(x_65);
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
x_111 = !lean_is_exclusive(x_103);
if (x_111 == 0)
{
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_103, 0);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_103);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_65);
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
x_115 = !lean_is_exclusive(x_97);
if (x_115 == 0)
{
return x_97;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_97, 0);
x_117 = lean_ctor_get(x_97, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_97);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
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
uint8_t x_119; 
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
x_119 = !lean_is_exclusive(x_21);
if (x_119 == 0)
{
return x_21;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_21, 0);
x_121 = lean_ctor_get(x_21, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_21);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
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
x_22 = l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
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
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it depends on index occurring at position #", 79);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_18 = l_List_elem___at_Lean_Meta_Occurrences_contains___spec__1(x_2, x_17);
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
lean_dec(x_11);
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
x_39 = l_Lean_MessageData_ofExpr(x_5);
x_40 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
x_46 = l_Nat_repr(x_45);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_51, x_9, x_10, x_11, x_12, x_38);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
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
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs in previous arguments", 67);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_17 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
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
x_24 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = l_Lean_MessageData_ofExpr(x_5);
x_27 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_indentExpr(x_8);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_34, x_10, x_11, x_12, x_13, x_25);
lean_dec(x_13);
lean_dec(x_11);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is an index in major premise, but it occurs more than once", 60);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_instInhabitedExpr;
x_58 = l___private_Init_Util_0__outOfBounds___rarg(x_57);
x_24 = x_58;
goto block_56;
}
else
{
lean_object* x_59; 
x_59 = lean_array_fget(x_5, x_21);
x_24 = x_59;
goto block_56;
}
block_56:
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
x_27 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2(x_6, x_21, x_3, x_24, x_7, x_2, x_1, x_4, x_26, x_11, x_12, x_13, x_14, x_15);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
x_34 = l_Lean_MessageData_ofExpr(x_7);
x_35 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_4);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
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
x_48 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_49 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2(x_6, x_21, x_3, x_24, x_7, x_2, x_1, x_4, x_48, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_10 = x_19;
x_15 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_15);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_get_size(x_1);
lean_inc(x_14);
lean_inc(x_7);
x_15 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2(x_2, x_3, x_4, x_5, x_1, x_6, x_7, x_14, x_14, x_14, x_9, x_10, x_11, x_12, x_13);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type index ", 25);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not a variable", 18);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_16 = l_Lean_MessageData_ofExpr(x_14);
x_17 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_6);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
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
x_31 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_3, x_4, x_5, x_6, x_2, x_14, x_30, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_22 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2(x_5, x_16, x_1, x_2, x_3, x_4, x_21, x_9, x_10, x_11, x_12, x_13);
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
x_34 = l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
x_15 = l_Lean_instInhabitedFVarId;
x_16 = l___private_Init_Util_0__outOfBounds___rarg(x_15);
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_37 = l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1(x_4, x_32, x_30, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
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
x_25 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__1(x_6, x_23, x_3, x_7, x_8, x_9, x_10, x_11, x_13, x_15, x_16, x_17, x_18, x_24);
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
x_31 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1;
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
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3;
x_37 = 0;
x_38 = l_Lean_Expr_lam___override(x_36, x_29, x_34, x_37);
x_39 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__1(x_6, x_26, x_3, x_7, x_8, x_9, x_10, x_11, x_38, x_15, x_16, x_17, x_18, x_35);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise is not of the form (C ...)", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4() {
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recursor '", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' can only eliminate into Prop", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
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
x_27 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4;
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___at_Lean_MVarId_induction___spec__5(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
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
x_35 = l_Lean_MessageData_ofName(x_1);
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8;
x_39 = lean_alloc_ctor(7, 2, 0);
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
x_46 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2(x_33, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_45, x_17, x_18, x_19, x_20, x_32);
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
x_50 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2(x_48, x_1, x_8, x_15, x_5, x_10, x_2, x_4, x_7, x_11, x_9, x_6, x_12, x_49, x_17, x_18, x_19, x_20, x_47);
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
x_61 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3;
x_62 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_61, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_18);
return x_62;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_37, x_38);
x_40 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1, x_11, x_12, x_13, x_20, x_26, x_37, x_41, x_43, x_14, x_15, x_16, x_17, x_36);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
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
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___boxed), 18, 13);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1() {
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("after revert&intro\n", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_13);
x_19 = lean_array_get_size(x_1);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_1);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_20, x_2, x_1);
x_22 = lean_array_push(x_21, x_3);
x_23 = 1;
x_24 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_25 = l_Lean_MVarId_revert(x_4, x_22, x_23, x_24, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_31 = l_Lean_Meta_introNCore(x_29, x_19, x_30, x_24, x_23, x_14, x_15, x_16, x_17, x_27);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
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
x_41 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1;
x_42 = l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4(x_34, x_1, x_20, x_2, x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_5);
x_44 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_5, x_14, x_15, x_16, x_17, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_34, x_2, x_39, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28, x_43, x_48, x_14, x_15, x_16, x_17, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
lean_inc(x_40);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_40);
x_52 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_5, x_55, x_14, x_15, x_16, x_17, x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_34, x_2, x_39, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28, x_43, x_57, x_14, x_15, x_16, x_17, x_58);
lean_dec(x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_36, 0);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_36);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
uint8_t x_68; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' does not support dependent elimination, but conclusion depends on major premise", 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_26, x_27, x_24, x_13, x_14, x_15, x_16, x_20);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_32, x_2, x_13, x_14, x_15, x_16, x_33);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_35 = x_53;
x_36 = x_52;
goto block_49;
}
else
{
uint8_t x_54; 
lean_dec(x_32);
x_54 = 0;
x_35 = x_54;
x_36 = x_33;
goto block_49;
}
block_49:
{
if (x_35 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_29, x_27, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_18, x_34, x_37, x_13, x_14, x_15, x_16, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = l_Lean_MessageData_ofName(x_3);
x_40 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_43, x_13, x_14, x_15, x_16, x_36);
lean_dec(x_16);
lean_dec(x_14);
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
}
else
{
uint8_t x_55; 
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
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
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
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
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
x_63 = !lean_is_exclusive(x_19);
if (x_63 == 0)
{
return x_19;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_19, 0);
x_65 = lean_ctor_get(x_19, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_19);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 1:
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_12);
lean_dec(x_10);
x_67 = lean_ctor_get(x_7, 5);
lean_inc(x_67);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_68 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_67, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_7, 6);
lean_inc(x_70);
x_71 = l_List_redLength___rarg(x_70);
x_72 = lean_mk_empty_array_with_capacity(x_71);
lean_dec(x_71);
x_73 = l_List_toArrayAux___rarg(x_70, x_72);
x_74 = lean_array_get_size(x_73);
x_75 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_76 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_77 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_75, x_76, x_73, x_13, x_14, x_15, x_16, x_69);
lean_dec(x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_1);
x_80 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_83 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_81, x_2, x_13, x_14, x_15, x_16, x_82);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_84 = x_102;
x_85 = x_101;
goto block_98;
}
else
{
uint8_t x_103; 
lean_dec(x_81);
x_103 = 0;
x_84 = x_103;
x_85 = x_82;
goto block_98;
}
block_98:
{
if (x_84 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_box(0);
x_87 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_78, x_76, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_67, x_83, x_86, x_13, x_14, x_15, x_16, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_78);
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = l_Lean_MessageData_ofName(x_3);
x_89 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_92, x_13, x_14, x_15, x_16, x_85);
lean_dec(x_16);
lean_dec(x_14);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_78);
lean_dec(x_67);
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
x_104 = !lean_is_exclusive(x_80);
if (x_104 == 0)
{
return x_80;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_80, 0);
x_106 = lean_ctor_get(x_80, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_80);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_67);
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
x_108 = !lean_is_exclusive(x_77);
if (x_108 == 0)
{
return x_77;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_77, 0);
x_110 = lean_ctor_get(x_77, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_77);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_67);
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
x_112 = !lean_is_exclusive(x_68);
if (x_112 == 0)
{
return x_68;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_68, 0);
x_114 = lean_ctor_get(x_68, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_68);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 2:
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
lean_dec(x_10);
x_116 = lean_ctor_get(x_7, 5);
lean_inc(x_116);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_117 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_116, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get(x_7, 6);
lean_inc(x_119);
x_120 = l_List_redLength___rarg(x_119);
x_121 = lean_mk_empty_array_with_capacity(x_120);
lean_dec(x_120);
x_122 = l_List_toArrayAux___rarg(x_119, x_121);
x_123 = lean_array_get_size(x_122);
x_124 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_125 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_126 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_124, x_125, x_122, x_13, x_14, x_15, x_16, x_118);
lean_dec(x_11);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_1);
x_129 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_132 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_130, x_2, x_13, x_14, x_15, x_16, x_131);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_133 = x_151;
x_134 = x_150;
goto block_147;
}
else
{
uint8_t x_152; 
lean_dec(x_130);
x_152 = 0;
x_133 = x_152;
x_134 = x_131;
goto block_147;
}
block_147:
{
if (x_133 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_box(0);
x_136 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_127, x_125, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_116, x_132, x_135, x_13, x_14, x_15, x_16, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_127);
lean_dec(x_116);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_137 = l_Lean_MessageData_ofName(x_3);
x_138 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_141, x_13, x_14, x_15, x_16, x_134);
lean_dec(x_16);
lean_dec(x_14);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
return x_142;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_142);
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
uint8_t x_153; 
lean_dec(x_127);
lean_dec(x_116);
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
x_153 = !lean_is_exclusive(x_129);
if (x_153 == 0)
{
return x_129;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_129, 0);
x_155 = lean_ctor_get(x_129, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_129);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_116);
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
x_157 = !lean_is_exclusive(x_126);
if (x_157 == 0)
{
return x_126;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_126, 0);
x_159 = lean_ctor_get(x_126, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_126);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_116);
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
x_161 = !lean_is_exclusive(x_117);
if (x_161 == 0)
{
return x_117;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_117, 0);
x_163 = lean_ctor_get(x_117, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
case 3:
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_12);
lean_dec(x_10);
x_165 = lean_ctor_get(x_7, 5);
lean_inc(x_165);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_166 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_165, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_ctor_get(x_7, 6);
lean_inc(x_168);
x_169 = l_List_redLength___rarg(x_168);
x_170 = lean_mk_empty_array_with_capacity(x_169);
lean_dec(x_169);
x_171 = l_List_toArrayAux___rarg(x_168, x_170);
x_172 = lean_array_get_size(x_171);
x_173 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_174 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_175 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_173, x_174, x_171, x_13, x_14, x_15, x_16, x_167);
lean_dec(x_11);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_1);
x_178 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_181 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_179, x_2, x_13, x_14, x_15, x_16, x_180);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_unbox(x_198);
lean_dec(x_198);
x_182 = x_200;
x_183 = x_199;
goto block_196;
}
else
{
uint8_t x_201; 
lean_dec(x_179);
x_201 = 0;
x_182 = x_201;
x_183 = x_180;
goto block_196;
}
block_196:
{
if (x_182 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(0);
x_185 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_176, x_174, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_165, x_181, x_184, x_13, x_14, x_15, x_16, x_183);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_176);
lean_dec(x_165);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_186 = l_Lean_MessageData_ofName(x_3);
x_187 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
x_189 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_190, x_13, x_14, x_15, x_16, x_183);
lean_dec(x_16);
lean_dec(x_14);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
return x_191;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_191);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_176);
lean_dec(x_165);
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
x_202 = !lean_is_exclusive(x_178);
if (x_202 == 0)
{
return x_178;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_178, 0);
x_204 = lean_ctor_get(x_178, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_178);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_165);
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
x_206 = !lean_is_exclusive(x_175);
if (x_206 == 0)
{
return x_175;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_175, 0);
x_208 = lean_ctor_get(x_175, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_175);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_165);
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
x_210 = !lean_is_exclusive(x_166);
if (x_210 == 0)
{
return x_166;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_166, 0);
x_212 = lean_ctor_get(x_166, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_166);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
case 4:
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_12);
lean_dec(x_10);
x_214 = lean_ctor_get(x_7, 5);
lean_inc(x_214);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_215 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_214, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; size_t x_222; size_t x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_7, 6);
lean_inc(x_217);
x_218 = l_List_redLength___rarg(x_217);
x_219 = lean_mk_empty_array_with_capacity(x_218);
lean_dec(x_218);
x_220 = l_List_toArrayAux___rarg(x_217, x_219);
x_221 = lean_array_get_size(x_220);
x_222 = lean_usize_of_nat(x_221);
lean_dec(x_221);
x_223 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_224 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_222, x_223, x_220, x_13, x_14, x_15, x_16, x_216);
lean_dec(x_11);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
lean_inc(x_1);
x_227 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_230 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_246 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_228, x_2, x_13, x_14, x_15, x_16, x_229);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_unbox(x_247);
lean_dec(x_247);
x_231 = x_249;
x_232 = x_248;
goto block_245;
}
else
{
uint8_t x_250; 
lean_dec(x_228);
x_250 = 0;
x_231 = x_250;
x_232 = x_229;
goto block_245;
}
block_245:
{
if (x_231 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_box(0);
x_234 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_225, x_223, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_214, x_230, x_233, x_13, x_14, x_15, x_16, x_232);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
lean_dec(x_225);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_235 = l_Lean_MessageData_ofName(x_3);
x_236 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_239, x_13, x_14, x_15, x_16, x_232);
lean_dec(x_16);
lean_dec(x_14);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
return x_240;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_240, 0);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_240);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_225);
lean_dec(x_214);
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
x_251 = !lean_is_exclusive(x_227);
if (x_251 == 0)
{
return x_227;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_227, 0);
x_253 = lean_ctor_get(x_227, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_227);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_214);
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
x_255 = !lean_is_exclusive(x_224);
if (x_255 == 0)
{
return x_224;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_224, 0);
x_257 = lean_ctor_get(x_224, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_224);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_214);
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
x_259 = !lean_is_exclusive(x_215);
if (x_259 == 0)
{
return x_215;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_215, 0);
x_261 = lean_ctor_get(x_215, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_215);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
case 5:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_10, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_10, 1);
lean_inc(x_264);
lean_dec(x_10);
x_265 = lean_array_set(x_11, x_12, x_264);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_sub(x_12, x_266);
lean_dec(x_12);
x_10 = x_263;
x_11 = x_265;
x_12 = x_267;
goto _start;
}
case 6:
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_12);
lean_dec(x_10);
x_269 = lean_ctor_get(x_7, 5);
lean_inc(x_269);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_270 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_269, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; size_t x_277; size_t x_278; lean_object* x_279; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_ctor_get(x_7, 6);
lean_inc(x_272);
x_273 = l_List_redLength___rarg(x_272);
x_274 = lean_mk_empty_array_with_capacity(x_273);
lean_dec(x_273);
x_275 = l_List_toArrayAux___rarg(x_272, x_274);
x_276 = lean_array_get_size(x_275);
x_277 = lean_usize_of_nat(x_276);
lean_dec(x_276);
x_278 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_279 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_277, x_278, x_275, x_13, x_14, x_15, x_16, x_271);
lean_dec(x_11);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_1);
x_282 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_285 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_283, x_2, x_13, x_14, x_15, x_16, x_284);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_unbox(x_302);
lean_dec(x_302);
x_286 = x_304;
x_287 = x_303;
goto block_300;
}
else
{
uint8_t x_305; 
lean_dec(x_283);
x_305 = 0;
x_286 = x_305;
x_287 = x_284;
goto block_300;
}
block_300:
{
if (x_286 == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_box(0);
x_289 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_280, x_278, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_269, x_285, x_288, x_13, x_14, x_15, x_16, x_287);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
lean_dec(x_280);
lean_dec(x_269);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_290 = l_Lean_MessageData_ofName(x_3);
x_291 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_294, x_13, x_14, x_15, x_16, x_287);
lean_dec(x_16);
lean_dec(x_14);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
return x_295;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_295, 0);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_295);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_280);
lean_dec(x_269);
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
x_306 = !lean_is_exclusive(x_282);
if (x_306 == 0)
{
return x_282;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_282, 0);
x_308 = lean_ctor_get(x_282, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_282);
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
lean_dec(x_269);
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
x_310 = !lean_is_exclusive(x_279);
if (x_310 == 0)
{
return x_279;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_279, 0);
x_312 = lean_ctor_get(x_279, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_279);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_269);
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
x_314 = !lean_is_exclusive(x_270);
if (x_314 == 0)
{
return x_270;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_270, 0);
x_316 = lean_ctor_get(x_270, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_270);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
case 7:
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_12);
lean_dec(x_10);
x_318 = lean_ctor_get(x_7, 5);
lean_inc(x_318);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_319 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_318, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; size_t x_326; size_t x_327; lean_object* x_328; 
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_ctor_get(x_7, 6);
lean_inc(x_321);
x_322 = l_List_redLength___rarg(x_321);
x_323 = lean_mk_empty_array_with_capacity(x_322);
lean_dec(x_322);
x_324 = l_List_toArrayAux___rarg(x_321, x_323);
x_325 = lean_array_get_size(x_324);
x_326 = lean_usize_of_nat(x_325);
lean_dec(x_325);
x_327 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_328 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_326, x_327, x_324, x_13, x_14, x_15, x_16, x_320);
lean_dec(x_11);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
lean_inc(x_1);
x_331 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_330);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_334 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_350 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_332, x_2, x_13, x_14, x_15, x_16, x_333);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_unbox(x_351);
lean_dec(x_351);
x_335 = x_353;
x_336 = x_352;
goto block_349;
}
else
{
uint8_t x_354; 
lean_dec(x_332);
x_354 = 0;
x_335 = x_354;
x_336 = x_333;
goto block_349;
}
block_349:
{
if (x_335 == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_box(0);
x_338 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_329, x_327, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_318, x_334, x_337, x_13, x_14, x_15, x_16, x_336);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_dec(x_329);
lean_dec(x_318);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_339 = l_Lean_MessageData_ofName(x_3);
x_340 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
x_342 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_343, x_13, x_14, x_15, x_16, x_336);
lean_dec(x_16);
lean_dec(x_14);
x_345 = !lean_is_exclusive(x_344);
if (x_345 == 0)
{
return x_344;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_344, 0);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_344);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
else
{
uint8_t x_355; 
lean_dec(x_329);
lean_dec(x_318);
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
x_355 = !lean_is_exclusive(x_331);
if (x_355 == 0)
{
return x_331;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_331, 0);
x_357 = lean_ctor_get(x_331, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_331);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_318);
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
x_359 = !lean_is_exclusive(x_328);
if (x_359 == 0)
{
return x_328;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_328, 0);
x_361 = lean_ctor_get(x_328, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_328);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
else
{
uint8_t x_363; 
lean_dec(x_318);
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
x_363 = !lean_is_exclusive(x_319);
if (x_363 == 0)
{
return x_319;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_319, 0);
x_365 = lean_ctor_get(x_319, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_319);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
case 8:
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_12);
lean_dec(x_10);
x_367 = lean_ctor_get(x_7, 5);
lean_inc(x_367);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_368 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_367, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; size_t x_375; size_t x_376; lean_object* x_377; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_ctor_get(x_7, 6);
lean_inc(x_370);
x_371 = l_List_redLength___rarg(x_370);
x_372 = lean_mk_empty_array_with_capacity(x_371);
lean_dec(x_371);
x_373 = l_List_toArrayAux___rarg(x_370, x_372);
x_374 = lean_array_get_size(x_373);
x_375 = lean_usize_of_nat(x_374);
lean_dec(x_374);
x_376 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_377 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_375, x_376, x_373, x_13, x_14, x_15, x_16, x_369);
lean_dec(x_11);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_1);
x_380 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_383 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_399 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_381, x_2, x_13, x_14, x_15, x_16, x_382);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_unbox(x_400);
lean_dec(x_400);
x_384 = x_402;
x_385 = x_401;
goto block_398;
}
else
{
uint8_t x_403; 
lean_dec(x_381);
x_403 = 0;
x_384 = x_403;
x_385 = x_382;
goto block_398;
}
block_398:
{
if (x_384 == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_box(0);
x_387 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_378, x_376, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_367, x_383, x_386, x_13, x_14, x_15, x_16, x_385);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
lean_dec(x_378);
lean_dec(x_367);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_388 = l_Lean_MessageData_ofName(x_3);
x_389 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_390 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_388);
x_391 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_392 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_392, x_13, x_14, x_15, x_16, x_385);
lean_dec(x_16);
lean_dec(x_14);
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
return x_393;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_393, 0);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_393);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
}
else
{
uint8_t x_404; 
lean_dec(x_378);
lean_dec(x_367);
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
x_404 = !lean_is_exclusive(x_380);
if (x_404 == 0)
{
return x_380;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_380, 0);
x_406 = lean_ctor_get(x_380, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_380);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_367);
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
x_408 = !lean_is_exclusive(x_377);
if (x_408 == 0)
{
return x_377;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_377, 0);
x_410 = lean_ctor_get(x_377, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_377);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_367);
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
x_412 = !lean_is_exclusive(x_368);
if (x_412 == 0)
{
return x_368;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_368, 0);
x_414 = lean_ctor_get(x_368, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_368);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
case 9:
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_12);
lean_dec(x_10);
x_416 = lean_ctor_get(x_7, 5);
lean_inc(x_416);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_417 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_416, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; size_t x_424; size_t x_425; lean_object* x_426; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get(x_7, 6);
lean_inc(x_419);
x_420 = l_List_redLength___rarg(x_419);
x_421 = lean_mk_empty_array_with_capacity(x_420);
lean_dec(x_420);
x_422 = l_List_toArrayAux___rarg(x_419, x_421);
x_423 = lean_array_get_size(x_422);
x_424 = lean_usize_of_nat(x_423);
lean_dec(x_423);
x_425 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_426 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_424, x_425, x_422, x_13, x_14, x_15, x_16, x_418);
lean_dec(x_11);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
lean_inc(x_1);
x_429 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_428);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; uint8_t x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_432 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_448 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_430, x_2, x_13, x_14, x_15, x_16, x_431);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_unbox(x_449);
lean_dec(x_449);
x_433 = x_451;
x_434 = x_450;
goto block_447;
}
else
{
uint8_t x_452; 
lean_dec(x_430);
x_452 = 0;
x_433 = x_452;
x_434 = x_431;
goto block_447;
}
block_447:
{
if (x_433 == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_box(0);
x_436 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_427, x_425, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_416, x_432, x_435, x_13, x_14, x_15, x_16, x_434);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
lean_dec(x_427);
lean_dec(x_416);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_437 = l_Lean_MessageData_ofName(x_3);
x_438 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_439 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
x_440 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_441, x_13, x_14, x_15, x_16, x_434);
lean_dec(x_16);
lean_dec(x_14);
x_443 = !lean_is_exclusive(x_442);
if (x_443 == 0)
{
return x_442;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_442, 0);
x_445 = lean_ctor_get(x_442, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_442);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_427);
lean_dec(x_416);
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
x_453 = !lean_is_exclusive(x_429);
if (x_453 == 0)
{
return x_429;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_429, 0);
x_455 = lean_ctor_get(x_429, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_429);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_416);
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
x_457 = !lean_is_exclusive(x_426);
if (x_457 == 0)
{
return x_426;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_426, 0);
x_459 = lean_ctor_get(x_426, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_426);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_416);
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
x_461 = !lean_is_exclusive(x_417);
if (x_461 == 0)
{
return x_417;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_417, 0);
x_463 = lean_ctor_get(x_417, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_417);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
case 10:
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_12);
lean_dec(x_10);
x_465 = lean_ctor_get(x_7, 5);
lean_inc(x_465);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_466 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_465, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; size_t x_473; size_t x_474; lean_object* x_475; 
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = lean_ctor_get(x_7, 6);
lean_inc(x_468);
x_469 = l_List_redLength___rarg(x_468);
x_470 = lean_mk_empty_array_with_capacity(x_469);
lean_dec(x_469);
x_471 = l_List_toArrayAux___rarg(x_468, x_470);
x_472 = lean_array_get_size(x_471);
x_473 = lean_usize_of_nat(x_472);
lean_dec(x_472);
x_474 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_475 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_473, x_474, x_471, x_13, x_14, x_15, x_16, x_467);
lean_dec(x_11);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
lean_inc(x_1);
x_478 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; uint8_t x_482; lean_object* x_483; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_481 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_481 == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_497 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_479, x_2, x_13, x_14, x_15, x_16, x_480);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_unbox(x_498);
lean_dec(x_498);
x_482 = x_500;
x_483 = x_499;
goto block_496;
}
else
{
uint8_t x_501; 
lean_dec(x_479);
x_501 = 0;
x_482 = x_501;
x_483 = x_480;
goto block_496;
}
block_496:
{
if (x_482 == 0)
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_box(0);
x_485 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_476, x_474, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_465, x_481, x_484, x_13, x_14, x_15, x_16, x_483);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
lean_dec(x_476);
lean_dec(x_465);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_486 = l_Lean_MessageData_ofName(x_3);
x_487 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_488 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_486);
x_489 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_490 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_490, x_13, x_14, x_15, x_16, x_483);
lean_dec(x_16);
lean_dec(x_14);
x_492 = !lean_is_exclusive(x_491);
if (x_492 == 0)
{
return x_491;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_491, 0);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_491);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_476);
lean_dec(x_465);
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
x_502 = !lean_is_exclusive(x_478);
if (x_502 == 0)
{
return x_478;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_478, 0);
x_504 = lean_ctor_get(x_478, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_478);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_465);
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
x_506 = !lean_is_exclusive(x_475);
if (x_506 == 0)
{
return x_475;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_475, 0);
x_508 = lean_ctor_get(x_475, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_475);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
uint8_t x_510; 
lean_dec(x_465);
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
x_510 = !lean_is_exclusive(x_466);
if (x_510 == 0)
{
return x_466;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_466, 0);
x_512 = lean_ctor_get(x_466, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_466);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
default: 
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_12);
lean_dec(x_10);
x_514 = lean_ctor_get(x_7, 5);
lean_inc(x_514);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_515 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_6, x_9, x_11, x_514, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; size_t x_522; size_t x_523; lean_object* x_524; 
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = lean_ctor_get(x_7, 6);
lean_inc(x_517);
x_518 = l_List_redLength___rarg(x_517);
x_519 = lean_mk_empty_array_with_capacity(x_518);
lean_dec(x_518);
x_520 = l_List_toArrayAux___rarg(x_517, x_519);
x_521 = lean_array_get_size(x_520);
x_522 = lean_usize_of_nat(x_521);
lean_dec(x_521);
x_523 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_524 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_6, x_7, x_9, x_11, x_522, x_523, x_520, x_13, x_14, x_15, x_16, x_516);
lean_dec(x_11);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
lean_inc(x_1);
x_527 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; uint8_t x_530; uint8_t x_531; lean_object* x_532; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_530 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_546 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__56(x_528, x_2, x_13, x_14, x_15, x_16, x_529);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_unbox(x_547);
lean_dec(x_547);
x_531 = x_549;
x_532 = x_548;
goto block_545;
}
else
{
uint8_t x_550; 
lean_dec(x_528);
x_550 = 0;
x_531 = x_550;
x_532 = x_529;
goto block_545;
}
block_545:
{
if (x_531 == 0)
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_box(0);
x_534 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_525, x_523, x_2, x_1, x_5, x_8, x_3, x_4, x_6, x_7, x_514, x_530, x_533, x_13, x_14, x_15, x_16, x_532);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
lean_dec(x_525);
lean_dec(x_514);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_535 = l_Lean_MessageData_ofName(x_3);
x_536 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6;
x_537 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2;
x_539 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_539, x_13, x_14, x_15, x_16, x_532);
lean_dec(x_16);
lean_dec(x_14);
x_541 = !lean_is_exclusive(x_540);
if (x_541 == 0)
{
return x_540;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_540, 0);
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_540);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_525);
lean_dec(x_514);
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
x_551 = !lean_is_exclusive(x_527);
if (x_551 == 0)
{
return x_527;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_527, 0);
x_553 = lean_ctor_get(x_527, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_527);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_514);
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
x_555 = !lean_is_exclusive(x_524);
if (x_555 == 0)
{
return x_524;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_524, 0);
x_557 = lean_ctor_get(x_524, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_524);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
else
{
uint8_t x_559; 
lean_dec(x_514);
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
x_559 = !lean_is_exclusive(x_515);
if (x_559 == 0)
{
return x_515;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_515, 0);
x_561 = lean_ctor_get(x_515, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_515);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
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
lean_inc(x_9);
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
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_29, x_30);
x_32 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_29);
x_36 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_12, x_20, x_23, x_29, x_29, x_33, x_35, x_7, x_8, x_9, x_10, x_28);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l_Lean_MVarId_induction___lambda__1(x_2, x_3, x_4, x_5, x_1, x_15, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_2);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = l_Lean_MVarId_induction___lambda__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_1);
x_23 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_22, x_6, x_7, x_8, x_9, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_MVarId_induction___lambda__1(x_2, x_3, x_4, x_5, x_1, x_24, x_6, x_7, x_8, x_9, x_25);
return x_26;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_induction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_induction___closed__1;
x_2 = l_Lean_MVarId_induction___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_MVarId_induction___closed__3;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lambda__2), 10, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_MVarId_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_MVarId_induction___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_List_foldlM___at_Lean_MVarId_induction___spec__5___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_MVarId_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_MVarId_induction___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___boxed(lean_object** _args) {
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
x_21 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___boxed(lean_object** _args) {
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
x_23 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___boxed(lean_object** _args) {
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
x_20 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
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
size_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_21 = lean_unbox(x_11);
lean_dec(x_11);
x_22 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__2(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___boxed(lean_object** _args) {
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
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
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
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2;
x_2 = l_Lean_MVarId_induction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8;
x_2 = l_Lean_MVarId_induction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9;
x_2 = l_Lean_MVarId_induction___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Induction", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14;
x_2 = lean_unsigned_to_nat(4054u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_MVarId_induction___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1 = _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1();
lean_mark_persistent(l_List_forM___at_Lean_MVarId_induction___spec__1___closed__1);
l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2 = _init_l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2();
lean_mark_persistent(l_List_forM___at_Lean_MVarId_induction___spec__1___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__3);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__1___closed__4);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___lambda__2___closed__2);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__1);
l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_MVarId_induction___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_induction___spec__3___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___lambda__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__4);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__5);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__6);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__7);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__6___closed__8);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___lambda__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__1);
l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_MVarId_induction___spec__7___closed__2);
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
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054____closed__15);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_4054_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
