// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__19___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__25;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__4;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__20___closed__4;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__23;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__16___boxed(lean_object**);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__15;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__13;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_substCore_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__17___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_heqToEq___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_substCore___spec__4___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__14;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__20;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object**);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object**);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__18___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__3;
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lambda__1___closed__1;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__26;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lambda__1___closed__2;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_substVar_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lambda__1___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__19___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__18___boxed(lean_object**);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lambda__1___closed__4;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__22;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839_(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__11;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object**);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
static lean_object* l_Lean_Meta_substVar___lambda__2___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__18___closed__1;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__20___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_heqToEq___lambda__2___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__10;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__20___closed__1;
static lean_object* l_Lean_Meta_substCore___lambda__20___closed__2;
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__8;
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__1;
static lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__17___closed__1;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__2;
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lambda__1___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__16;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__21(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__14___boxed(lean_object**);
static lean_object* l_Lean_Meta_substCore___lambda__14___closed__3;
static lean_object* l_Lean_Meta_subst_substEq___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object**);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_substCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__7;
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__17;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_heqToEq___lambda__2___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lambda__2___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5(size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__21___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_nat_dec_lt(x_19, x_2);
x_21 = lean_array_get_size(x_3);
x_22 = lean_nat_dec_lt(x_17, x_21);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l_Lean_instInhabitedFVarId;
x_24 = l_outOfBounds___rarg(x_23);
if (x_22 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = l_outOfBounds___rarg(x_23);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_26);
x_5 = x_15;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_30);
x_5 = x_15;
x_6 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_1, x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
x_34 = l_Lean_instInhabitedFVarId;
x_35 = l_outOfBounds___rarg(x_34);
x_36 = l_Lean_Expr_fvar___override(x_35);
x_37 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_36);
x_5 = x_15;
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_40 = l_Lean_Expr_fvar___override(x_39);
x_41 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_40);
x_5 = x_15;
x_6 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_nat_dec_lt(x_19, x_2);
x_21 = lean_array_get_size(x_3);
x_22 = lean_nat_dec_lt(x_17, x_21);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l_Lean_instInhabitedFVarId;
x_24 = l_outOfBounds___rarg(x_23);
if (x_22 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = l_outOfBounds___rarg(x_23);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_26);
x_5 = x_15;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_30);
x_5 = x_15;
x_6 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_1, x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
x_34 = l_Lean_instInhabitedFVarId;
x_35 = l_outOfBounds___rarg(x_34);
x_36 = l_Lean_Expr_fvar___override(x_35);
x_37 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_36);
x_5 = x_15;
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_40 = l_Lean_Expr_fvar___override(x_39);
x_41 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_40);
x_5 = x_15;
x_6 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_nat_dec_lt(x_19, x_2);
x_21 = lean_array_get_size(x_3);
x_22 = lean_nat_dec_lt(x_17, x_21);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l_Lean_instInhabitedFVarId;
x_24 = l_outOfBounds___rarg(x_23);
if (x_22 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = l_outOfBounds___rarg(x_23);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_26);
x_5 = x_15;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = l_Lean_Meta_FVarSubst_insert(x_6, x_24, x_30);
x_5 = x_15;
x_6 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_1, x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
x_34 = l_Lean_instInhabitedFVarId;
x_35 = l_outOfBounds___rarg(x_34);
x_36 = l_Lean_Expr_fvar___override(x_35);
x_37 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_36);
x_5 = x_15;
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_40 = l_Lean_Expr_fvar___override(x_39);
x_41 = l_Lean_Meta_FVarSubst_insert(x_6, x_33, x_40);
x_5 = x_15;
x_6 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_substCore___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_substCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_substCore___spec__4___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_get_size(x_1);
lean_inc(x_18);
x_19 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_2, x_3, x_1, x_18, x_18, x_4, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_18);
if (x_5 == 0)
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_FVarSubst_insert(x_21, x_6, x_7);
x_23 = l_Lean_Meta_FVarSubst_insert(x_22, x_8, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l_Lean_Meta_FVarSubst_insert(x_25, x_6, x_7);
x_28 = l_Lean_Meta_FVarSubst_insert(x_27, x_8, x_9);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = l_Lean_Meta_FVarSubst_insert(x_32, x_6, x_11);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_8, x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = l_Lean_Meta_FVarSubst_insert(x_36, x_6, x_11);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_8, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after intro rest ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_sub(x_17, x_18);
x_20 = 0;
x_21 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_22 = l_Lean_Meta_introNCore(x_11, x_19, x_2, x_20, x_21, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_3);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_substCore___lambda__1(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_32, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_26);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = l_Lean_Meta_substCore___lambda__2___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_39);
lean_ctor_set(x_28, 0, x_40);
x_41 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_28);
lean_inc(x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_27);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_45, x_12, x_13, x_14, x_15, x_35);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_substCore___lambda__1(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_47, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_47);
lean_dec(x_17);
lean_dec(x_26);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_56);
lean_ctor_set(x_23, 0, x_55);
lean_inc(x_27);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_27);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_60, x_12, x_13, x_14, x_15, x_50);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_substCore___lambda__1(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_62, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_62);
lean_dec(x_17);
lean_dec(x_26);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_23, 0);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_23);
lean_inc(x_3);
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_19);
lean_dec(x_3);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_substCore___lambda__1(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_71, x_12, x_13, x_14, x_15, x_70);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_65);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = l_Lean_Meta_substCore___lambda__2___closed__2;
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_74;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_substCore___lambda__2___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_66);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_66);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_85, x_12, x_13, x_14, x_15, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_substCore___lambda__1(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_87, x_12, x_13, x_14, x_15, x_88);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_87);
lean_dec(x_17);
lean_dec(x_65);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_22);
if (x_90 == 0)
{
return x_22;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_22, 0);
x_92 = lean_ctor_get(x_22, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_22);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_15, x_16, x_17, x_18, x_19, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_mvarId_x21(x_2);
if (x_7 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
x_24 = l_Lean_Meta_substCore___lambda__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23, x_16, x_17, x_18, x_19, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_MVarId_clear(x_23, x_13, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_28 = l_Lean_MVarId_clear(x_26, x_14, x_16, x_17, x_18, x_19, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_substCore___lambda__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_29, x_16, x_17, x_18, x_19, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_18);
x_23 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_18, x_19, x_20, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_24);
x_26 = l_Lean_Meta_mkEqNDRec(x_16, x_24, x_17, x_18, x_19, x_20, x_21, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_substCore___lambda__3(x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27, x_18, x_19, x_20, x_21, x_28);
lean_dec(x_24);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_replaceFVar(x_1, x_2, x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_mk(x_16);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_17, x_14, x_18, x_19, x_18, x_20, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_get_size(x_1);
lean_inc(x_18);
x_19 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2(x_2, x_3, x_1, x_18, x_18, x_4, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_18);
if (x_5 == 0)
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_FVarSubst_insert(x_21, x_6, x_7);
x_23 = l_Lean_Meta_FVarSubst_insert(x_22, x_8, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l_Lean_Meta_FVarSubst_insert(x_25, x_6, x_7);
x_28 = l_Lean_Meta_FVarSubst_insert(x_27, x_8, x_9);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = l_Lean_Meta_FVarSubst_insert(x_32, x_6, x_11);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_8, x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = l_Lean_Meta_FVarSubst_insert(x_36, x_6, x_11);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_8, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_sub(x_17, x_18);
x_20 = 0;
x_21 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_22 = l_Lean_Meta_introNCore(x_11, x_19, x_2, x_20, x_21, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_3);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_substCore___lambda__6(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_32, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_26);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = l_Lean_Meta_substCore___lambda__2___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_39);
lean_ctor_set(x_28, 0, x_40);
x_41 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_28);
lean_inc(x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_27);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_45, x_12, x_13, x_14, x_15, x_35);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_substCore___lambda__6(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_47, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_47);
lean_dec(x_17);
lean_dec(x_26);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_56);
lean_ctor_set(x_23, 0, x_55);
lean_inc(x_27);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_27);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_60, x_12, x_13, x_14, x_15, x_50);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_substCore___lambda__6(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_62, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_62);
lean_dec(x_17);
lean_dec(x_26);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_23, 0);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_23);
lean_inc(x_3);
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_19);
lean_dec(x_3);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_substCore___lambda__6(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_71, x_12, x_13, x_14, x_15, x_70);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_65);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = l_Lean_Meta_substCore___lambda__2___closed__2;
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_74;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_substCore___lambda__2___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_66);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_66);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_85, x_12, x_13, x_14, x_15, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_substCore___lambda__6(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_87, x_12, x_13, x_14, x_15, x_88);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_87);
lean_dec(x_17);
lean_dec(x_65);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_22);
if (x_90 == 0)
{
return x_22;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_22, 0);
x_92 = lean_ctor_get(x_22, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_22);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_15, x_16, x_17, x_18, x_19, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_mvarId_x21(x_2);
if (x_7 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
x_24 = l_Lean_Meta_substCore___lambda__7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23, x_16, x_17, x_18, x_19, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_MVarId_clear(x_23, x_13, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_28 = l_Lean_MVarId_clear(x_26, x_14, x_16, x_17, x_18, x_19, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_substCore___lambda__7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_29, x_16, x_17, x_18, x_19, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_18);
x_23 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_18, x_19, x_20, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_24);
x_26 = l_Lean_Meta_mkEqRec(x_16, x_24, x_17, x_18, x_19, x_20, x_21, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_substCore___lambda__8(x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27, x_18, x_19, x_20, x_21, x_28);
lean_dec(x_24);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_get_size(x_1);
lean_inc(x_18);
x_19 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3(x_2, x_3, x_1, x_18, x_18, x_4, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_18);
if (x_5 == 0)
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_FVarSubst_insert(x_21, x_6, x_7);
x_23 = l_Lean_Meta_FVarSubst_insert(x_22, x_8, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l_Lean_Meta_FVarSubst_insert(x_25, x_6, x_7);
x_28 = l_Lean_Meta_FVarSubst_insert(x_27, x_8, x_9);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = l_Lean_Meta_FVarSubst_insert(x_32, x_6, x_11);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_8, x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = l_Lean_Meta_FVarSubst_insert(x_36, x_6, x_11);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_8, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_sub(x_17, x_18);
x_20 = 0;
x_21 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_22 = l_Lean_Meta_introNCore(x_11, x_19, x_2, x_20, x_21, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_3);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_substCore___lambda__10(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_32, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_26);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = l_Lean_Meta_substCore___lambda__2___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_39);
lean_ctor_set(x_28, 0, x_40);
x_41 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_28);
lean_inc(x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_27);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_45, x_12, x_13, x_14, x_15, x_35);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_substCore___lambda__10(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_47, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_47);
lean_dec(x_17);
lean_dec(x_26);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_substCore___lambda__2___closed__4;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_56);
lean_ctor_set(x_23, 0, x_55);
lean_inc(x_27);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_27);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_60, x_12, x_13, x_14, x_15, x_50);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_substCore___lambda__10(x_26, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_10, x_62, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_62);
lean_dec(x_17);
lean_dec(x_26);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_23, 0);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_23);
lean_inc(x_3);
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_12, x_13, x_14, x_15, x_24);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_19);
lean_dec(x_3);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_substCore___lambda__10(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_71, x_12, x_13, x_14, x_15, x_70);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_17);
lean_dec(x_65);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = l_Lean_Meta_substCore___lambda__2___closed__2;
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_74;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_substCore___lambda__2___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_66);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_66);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_85, x_12, x_13, x_14, x_15, x_73);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_substCore___lambda__10(x_65, x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_66, x_10, x_87, x_12, x_13, x_14, x_15, x_88);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_87);
lean_dec(x_17);
lean_dec(x_65);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_22);
if (x_90 == 0)
{
return x_22;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_22, 0);
x_92 = lean_ctor_get(x_22, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_22);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_15, x_16, x_17, x_18, x_19, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_mvarId_x21(x_2);
if (x_7 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
x_24 = l_Lean_Meta_substCore___lambda__11(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23, x_16, x_17, x_18, x_19, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_MVarId_clear(x_23, x_13, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_28 = l_Lean_MVarId_clear(x_26, x_14, x_16, x_17, x_18, x_19, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_substCore___lambda__11(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_29, x_16, x_17, x_18, x_19, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_18);
x_23 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_18, x_19, x_20, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_24);
x_26 = l_Lean_Meta_mkEqRec(x_16, x_24, x_17, x_18, x_19, x_20, x_21, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_substCore___lambda__12(x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27, x_18, x_19, x_20, x_21, x_28);
lean_dec(x_24);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_h", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__14___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Subst", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.substCore", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__14___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lambda__14___closed__3;
x_2 = l_Lean_Meta_substCore___lambda__14___closed__4;
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_substCore___lambda__14___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_1);
x_20 = l_Lean_MVarId_getDecl(x_1, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_15);
lean_inc(x_2);
x_24 = l_Lean_FVarId_getDecl(x_2, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_type(x_25);
lean_dec(x_25);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_28 = l_Lean_Meta_matchEq_x3f(x_27, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = l_Lean_Meta_substCore___lambda__14___closed__6;
x_267 = l_panic___at_Lean_Meta_substCore___spec__4(x_266, x_15, x_16, x_17, x_18, x_30);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_29, 0);
lean_inc(x_268);
lean_dec(x_29);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
if (x_14 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_31 = x_270;
goto block_265;
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
x_31 = x_271;
goto block_265;
}
}
block_265:
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_31, x_15, x_16, x_17, x_18, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_23);
x_36 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_23, x_2, x_15, x_16, x_17, x_18, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_free_object(x_32);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
lean_inc(x_4);
lean_inc(x_3);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 0, x_3);
x_42 = lean_array_mk(x_36);
x_43 = 0;
x_44 = 1;
x_45 = 1;
lean_inc(x_23);
x_46 = l_Lean_Meta_mkLambdaFVars(x_42, x_23, x_43, x_44, x_43, x_45, x_15, x_16, x_17, x_18, x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_3);
x_49 = l_Lean_Expr_replaceFVar(x_23, x_3, x_34);
lean_dec(x_23);
if (x_14 == 0)
{
lean_object* x_50; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_50 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_substCore___lambda__4(x_49, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_47, x_51, x_15, x_16, x_17, x_18, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
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
lean_inc(x_12);
x_58 = l_Lean_Meta_substCore___lambda__4(x_49, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_47, x_12, x_15, x_16, x_17, x_18, x_48);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_dec(x_36);
lean_inc(x_4);
lean_inc(x_3);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_3);
lean_ctor_set(x_64, 1, x_4);
x_65 = lean_array_mk(x_64);
x_66 = 0;
x_67 = 1;
x_68 = 1;
lean_inc(x_23);
x_69 = l_Lean_Meta_mkLambdaFVars(x_65, x_23, x_66, x_67, x_66, x_68, x_15, x_16, x_17, x_18, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_3);
x_72 = l_Lean_Expr_replaceFVar(x_23, x_3, x_34);
lean_dec(x_23);
if (x_14 == 0)
{
lean_object* x_73; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_73 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_substCore___lambda__4(x_72, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_70, x_74, x_15, x_16, x_17, x_18, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
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
lean_object* x_81; 
lean_inc(x_12);
x_81 = l_Lean_Meta_substCore___lambda__4(x_72, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_70, x_12, x_15, x_16, x_17, x_18, x_71);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_69, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_84 = x_69;
} else {
 lean_dec_ref(x_69);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_36, 1);
x_88 = lean_ctor_get(x_36, 0);
lean_dec(x_88);
lean_inc(x_3);
x_89 = l_Lean_Expr_replaceFVar(x_23, x_3, x_34);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_34);
x_90 = l_Lean_Meta_mkEqRefl(x_34, x_15, x_16, x_17, x_18, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_12);
x_93 = l_Lean_Expr_replaceFVar(x_89, x_12, x_91);
lean_dec(x_91);
lean_dec(x_89);
if (x_14 == 0)
{
lean_object* x_94; 
lean_free_object(x_36);
lean_free_object(x_32);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_34);
x_94 = l_Lean_Meta_mkEq(x_34, x_3, x_15, x_16, x_17, x_18, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_12);
x_97 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__5___boxed), 10, 4);
lean_closure_set(x_97, 0, x_23);
lean_closure_set(x_97, 1, x_12);
lean_closure_set(x_97, 2, x_4);
lean_closure_set(x_97, 3, x_3);
x_98 = l_Lean_Meta_substCore___lambda__14___closed__2;
x_99 = 0;
x_100 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_101 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_98, x_99, x_95, x_97, x_100, x_15, x_16, x_17, x_18, x_96);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_104 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_substCore___lambda__9(x_93, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_102, x_105, x_15, x_16, x_17, x_18, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_102);
lean_dec(x_93);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_104);
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
lean_dec(x_93);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_101);
if (x_112 == 0)
{
return x_101;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_101, 0);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_101);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_93);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_94);
if (x_116 == 0)
{
return x_94;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_94, 0);
x_118 = lean_ctor_get(x_94, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_94);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; 
lean_inc(x_4);
lean_inc(x_12);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 0, x_12);
lean_inc(x_3);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_36);
lean_ctor_set(x_32, 0, x_3);
x_120 = lean_array_mk(x_32);
x_121 = 0;
x_122 = 1;
x_123 = 1;
x_124 = l_Lean_Meta_mkLambdaFVars(x_120, x_23, x_121, x_122, x_121, x_123, x_15, x_16, x_17, x_18, x_92);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_12);
x_127 = l_Lean_Meta_substCore___lambda__13(x_93, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_125, x_12, x_15, x_16, x_17, x_18, x_126);
return x_127;
}
else
{
uint8_t x_128; 
lean_dec(x_93);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_124);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_89);
lean_free_object(x_36);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_90);
if (x_132 == 0)
{
return x_90;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_90, 0);
x_134 = lean_ctor_get(x_90, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_90);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_36, 1);
lean_inc(x_136);
lean_dec(x_36);
lean_inc(x_3);
x_137 = l_Lean_Expr_replaceFVar(x_23, x_3, x_34);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_34);
x_138 = l_Lean_Meta_mkEqRefl(x_34, x_15, x_16, x_17, x_18, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_12);
x_141 = l_Lean_Expr_replaceFVar(x_137, x_12, x_139);
lean_dec(x_139);
lean_dec(x_137);
if (x_14 == 0)
{
lean_object* x_142; 
lean_free_object(x_32);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_34);
x_142 = l_Lean_Meta_mkEq(x_34, x_3, x_15, x_16, x_17, x_18, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_12);
x_145 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__5___boxed), 10, 4);
lean_closure_set(x_145, 0, x_23);
lean_closure_set(x_145, 1, x_12);
lean_closure_set(x_145, 2, x_4);
lean_closure_set(x_145, 3, x_3);
x_146 = l_Lean_Meta_substCore___lambda__14___closed__2;
x_147 = 0;
x_148 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_149 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_146, x_147, x_143, x_145, x_148, x_15, x_16, x_17, x_18, x_144);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_152 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_substCore___lambda__9(x_141, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_150, x_153, x_15, x_16, x_17, x_18, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_158 = x_152;
} else {
 lean_dec_ref(x_152);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_141);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_149, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_149, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_162 = x_149;
} else {
 lean_dec_ref(x_149);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_141);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_142, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_142, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_166 = x_142;
} else {
 lean_dec_ref(x_142);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
lean_inc(x_4);
lean_inc(x_12);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_12);
lean_ctor_set(x_168, 1, x_4);
lean_inc(x_3);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_168);
lean_ctor_set(x_32, 0, x_3);
x_169 = lean_array_mk(x_32);
x_170 = 0;
x_171 = 1;
x_172 = 1;
x_173 = l_Lean_Meta_mkLambdaFVars(x_169, x_23, x_170, x_171, x_170, x_172, x_15, x_16, x_17, x_18, x_140);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_12);
x_176 = l_Lean_Meta_substCore___lambda__13(x_141, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_34, x_2, x_13, x_174, x_12, x_15, x_16, x_17, x_18, x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_141);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_137);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_138, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_138, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_183 = x_138;
} else {
 lean_dec_ref(x_138);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_32, 0);
x_186 = lean_ctor_get(x_32, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_32);
lean_inc(x_23);
x_187 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_23, x_2, x_15, x_16, x_17, x_18, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
 lean_ctor_set_tag(x_192, 1);
}
lean_ctor_set(x_192, 0, x_3);
lean_ctor_set(x_192, 1, x_4);
x_193 = lean_array_mk(x_192);
x_194 = 0;
x_195 = 1;
x_196 = 1;
lean_inc(x_23);
x_197 = l_Lean_Meta_mkLambdaFVars(x_193, x_23, x_194, x_195, x_194, x_196, x_15, x_16, x_17, x_18, x_190);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
lean_inc(x_3);
x_200 = l_Lean_Expr_replaceFVar(x_23, x_3, x_185);
lean_dec(x_23);
if (x_14 == 0)
{
lean_object* x_201; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_201 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_199);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_Meta_substCore___lambda__4(x_200, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_185, x_2, x_13, x_198, x_202, x_15, x_16, x_17, x_18, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_inc(x_12);
x_209 = l_Lean_Meta_substCore___lambda__4(x_200, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_185, x_2, x_13, x_198, x_12, x_15, x_16, x_17, x_18, x_199);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_185);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_212 = x_197;
} else {
 lean_dec_ref(x_197);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_187, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_215 = x_187;
} else {
 lean_dec_ref(x_187);
 x_215 = lean_box(0);
}
lean_inc(x_3);
x_216 = l_Lean_Expr_replaceFVar(x_23, x_3, x_185);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_185);
x_217 = l_Lean_Meta_mkEqRefl(x_185, x_15, x_16, x_17, x_18, x_214);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_12);
x_220 = l_Lean_Expr_replaceFVar(x_216, x_12, x_218);
lean_dec(x_218);
lean_dec(x_216);
if (x_14 == 0)
{
lean_object* x_221; 
lean_dec(x_215);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_185);
x_221 = l_Lean_Meta_mkEq(x_185, x_3, x_15, x_16, x_17, x_18, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_12);
x_224 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__5___boxed), 10, 4);
lean_closure_set(x_224, 0, x_23);
lean_closure_set(x_224, 1, x_12);
lean_closure_set(x_224, 2, x_4);
lean_closure_set(x_224, 3, x_3);
x_225 = l_Lean_Meta_substCore___lambda__14___closed__2;
x_226 = 0;
x_227 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_228 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_225, x_226, x_222, x_224, x_227, x_15, x_16, x_17, x_18, x_223);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_231 = l_Lean_Meta_mkEqSymm(x_12, x_15, x_16, x_17, x_18, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Lean_Meta_substCore___lambda__9(x_220, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_185, x_2, x_13, x_229, x_232, x_15, x_16, x_17, x_18, x_233);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_229);
lean_dec(x_220);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_220);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_ctor_get(x_228, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_228, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_241 = x_228;
} else {
 lean_dec_ref(x_228);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_220);
lean_dec(x_185);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lean_ctor_get(x_221, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_221, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_245 = x_221;
} else {
 lean_dec_ref(x_221);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; 
lean_inc(x_4);
lean_inc(x_12);
if (lean_is_scalar(x_215)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_215;
 lean_ctor_set_tag(x_247, 1);
}
lean_ctor_set(x_247, 0, x_12);
lean_ctor_set(x_247, 1, x_4);
lean_inc(x_3);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_3);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_array_mk(x_248);
x_250 = 0;
x_251 = 1;
x_252 = 1;
x_253 = l_Lean_Meta_mkLambdaFVars(x_249, x_23, x_250, x_251, x_250, x_252, x_15, x_16, x_17, x_18, x_219);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
lean_inc(x_12);
x_256 = l_Lean_Meta_substCore___lambda__13(x_220, x_5, x_1, x_6, x_4, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_185, x_2, x_13, x_254, x_12, x_15, x_16, x_17, x_18, x_255);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_220);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_253, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
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
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_217, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_217, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_263 = x_217;
} else {
 lean_dec_ref(x_217);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_28);
if (x_272 == 0)
{
return x_28;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_28, 0);
x_274 = lean_ctor_get(x_28, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_28);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_24);
if (x_276 == 0)
{
return x_24;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_24, 0);
x_278 = lean_ctor_get(x_24, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_24);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_20);
if (x_280 == 0)
{
return x_20;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_20, 0);
x_282 = lean_ctor_get(x_20, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_20);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (x_15 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_box(x_9);
x_22 = lean_box(x_14);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__14___boxed), 19, 14);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_8);
lean_closure_set(x_23, 8, x_21);
lean_closure_set(x_23, 9, x_10);
lean_closure_set(x_23, 10, x_11);
lean_closure_set(x_23, 11, x_12);
lean_closure_set(x_23, 12, x_13);
lean_closure_set(x_23, 13, x_22);
x_24 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_23, x_16, x_17, x_18, x_19, x_20);
return x_24;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (x_9 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_27 = l_Lean_MVarId_clear(x_1, x_2, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_MVarId_clear(x_28, x_13, x_16, x_17, x_18, x_19, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_array_get_size(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_dec_lt(x_22, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_instInhabitedFVarId;
x_64 = l_outOfBounds___rarg(x_63);
x_24 = x_64;
goto block_62;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget(x_1, x_20);
x_24 = x_65;
goto block_62;
}
block_62:
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_24);
x_25 = l_Lean_Expr_fvar___override(x_24);
if (x_23 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_instInhabitedFVarId;
x_60 = l_outOfBounds___rarg(x_59);
x_26 = x_60;
goto block_58;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget(x_1, x_22);
x_26 = x_61;
goto block_58;
}
block_58:
{
lean_object* x_27; 
lean_inc(x_26);
x_27 = l_Lean_Expr_fvar___override(x_26);
if (x_12 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
x_29 = l_Lean_Meta_substCore___lambda__15(x_2, x_26, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_24, x_11, x_28, x_14, x_15, x_16, x_17, x_18);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_5);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; 
x_33 = 0;
x_34 = l_Lean_Meta_substCore___lambda__15(x_2, x_26, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_24, x_11, x_33, x_14, x_15, x_16, x_17, x_18);
return x_34;
}
else
{
lean_object* x_35; 
lean_inc(x_2);
x_35 = l_Lean_MVarId_getType(x_2, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_36);
x_38 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_36, x_24, x_14, x_15, x_16, x_17, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_36, x_26, x_14, x_15, x_16, x_17, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = 1;
x_47 = l_Lean_Meta_substCore___lambda__15(x_2, x_26, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_24, x_11, x_46, x_14, x_15, x_16, x_17, x_45);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = 0;
x_50 = l_Lean_Meta_substCore___lambda__15(x_2, x_26, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_24, x_11, x_49, x_14, x_15, x_16, x_17, x_48);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
lean_dec(x_36);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
x_52 = 0;
x_53 = l_Lean_Meta_substCore___lambda__15(x_2, x_26, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_24, x_11, x_52, x_14, x_15, x_16, x_17, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_35);
if (x_54 == 0)
{
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_35, 0);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_35);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reverted variables ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__17___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_19 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_14, x_15, x_16, x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_substCore___lambda__16(x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_23, x_14, x_15, x_16, x_17, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_array_size(x_6);
x_29 = 0;
lean_inc(x_6);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5(x_28, x_29, x_6);
x_31 = lean_array_to_list(x_30);
lean_inc(x_4);
x_32 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_31, x_4);
x_33 = l_Lean_MessageData_ofList(x_32);
x_34 = l_Lean_Meta_substCore___lambda__17___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_34);
x_35 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_1);
x_37 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_36, x_14, x_15, x_16, x_17, x_26);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_substCore___lambda__16(x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_38, x_14, x_15, x_16, x_17, x_39);
lean_dec(x_38);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_array_size(x_6);
x_43 = 0;
lean_inc(x_6);
x_44 = l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5(x_42, x_43, x_6);
x_45 = lean_array_to_list(x_44);
lean_inc(x_4);
x_46 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_45, x_4);
x_47 = l_Lean_MessageData_ofList(x_46);
x_48 = l_Lean_Meta_substCore___lambda__17___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_1);
x_52 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_51, x_14, x_15, x_16, x_17, x_41);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_substCore___lambda__16(x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_53, x_14, x_15, x_16, x_17, x_54);
lean_dec(x_53);
return x_55;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__18___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after intro2 ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__18___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__18___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = 0;
x_20 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_21 = l_Lean_Meta_introNCore(x_1, x_18, x_2, x_19, x_20, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_3);
x_27 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_13, x_14, x_15, x_16, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_22);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_substCore___lambda__17(x_3, x_25, x_26, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31, x_13, x_14, x_15, x_16, x_30);
lean_dec(x_25);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
lean_inc(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_26);
x_37 = l_Lean_Meta_substCore___lambda__18___closed__2;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_37);
x_38 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_38);
lean_ctor_set(x_22, 0, x_27);
lean_inc(x_3);
x_39 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_22, x_13, x_14, x_15, x_16, x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_substCore___lambda__17(x_3, x_25, x_26, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40, x_13, x_14, x_15, x_16, x_41);
lean_dec(x_40);
lean_dec(x_25);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
lean_inc(x_26);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_26);
x_45 = l_Lean_Meta_substCore___lambda__18___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_47);
lean_ctor_set(x_22, 0, x_46);
lean_inc(x_3);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_22, x_13, x_14, x_15, x_16, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_substCore___lambda__17(x_3, x_25, x_26, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_49, x_13, x_14, x_15, x_16, x_50);
lean_dec(x_49);
lean_dec(x_25);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
lean_inc(x_3);
x_54 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_13, x_14, x_15, x_16, x_23);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_substCore___lambda__17(x_3, x_52, x_53, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58, x_13, x_14, x_15, x_16, x_57);
lean_dec(x_52);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
lean_inc(x_53);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_53);
x_63 = l_Lean_Meta_substCore___lambda__18___closed__2;
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_61;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_3);
x_67 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_66, x_13, x_14, x_15, x_16, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_substCore___lambda__17(x_3, x_52, x_53, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_68, x_13, x_14, x_15, x_16, x_69);
lean_dec(x_68);
lean_dec(x_52);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
return x_21;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__19___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after revert ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__19___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__19___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = 1;
x_21 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_MVarId_revert(x_3, x_19, x_20, x_21, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_4);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_11, x_12, x_13, x_14, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_substCore___lambda__18(x_27, x_16, x_4, x_5, x_26, x_6, x_7, x_2, x_1, x_8, x_9, x_32, x_11, x_12, x_13, x_14, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
lean_inc(x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_27);
x_38 = l_Lean_Meta_substCore___lambda__19___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_38);
x_39 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_39);
lean_ctor_set(x_23, 0, x_28);
lean_inc(x_4);
x_40 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_23, x_11, x_12, x_13, x_14, x_35);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_substCore___lambda__18(x_27, x_16, x_4, x_5, x_26, x_6, x_7, x_2, x_1, x_8, x_9, x_41, x_11, x_12, x_13, x_14, x_42);
lean_dec(x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
lean_inc(x_27);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_27);
x_46 = l_Lean_Meta_substCore___lambda__19___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_48);
lean_ctor_set(x_23, 0, x_47);
lean_inc(x_4);
x_49 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_23, x_11, x_12, x_13, x_14, x_44);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_substCore___lambda__18(x_27, x_16, x_4, x_5, x_26, x_6, x_7, x_2, x_1, x_8, x_9, x_50, x_11, x_12, x_13, x_14, x_51);
lean_dec(x_50);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
lean_inc(x_4);
x_55 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_11, x_12, x_13, x_14, x_24);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_substCore___lambda__18(x_54, x_16, x_4, x_5, x_53, x_6, x_7, x_2, x_1, x_8, x_9, x_59, x_11, x_12, x_13, x_14, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
lean_inc(x_54);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_54);
x_64 = l_Lean_Meta_substCore___lambda__19___closed__2;
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(7, 2, 0);
} else {
 x_65 = x_62;
 lean_ctor_set_tag(x_65, 7);
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_4);
x_68 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_67, x_11, x_12, x_13, x_14, x_61);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_substCore___lambda__18(x_54, x_16, x_4, x_5, x_53, x_6, x_7, x_2, x_1, x_8, x_9, x_69, x_11, x_12, x_13, x_14, x_70);
lean_dec(x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_22, 0);
x_74 = lean_ctor_get(x_22, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_22);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__20___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__20___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__20___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__20___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' occurs at", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__20___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__20___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_19 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_1, x_2, x_14, x_15, x_16, x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_substCore___lambda__19(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23, x_14, x_15, x_16, x_17, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = l_Lean_MessageData_ofExpr(x_11);
x_29 = l_Lean_Meta_substCore___lambda__20___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_29);
x_30 = l_Lean_Meta_substCore___lambda__20___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_1);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_4, x_36, x_14, x_15, x_16, x_17, x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Lean_MessageData_ofExpr(x_11);
x_44 = l_Lean_Meta_substCore___lambda__20___closed__2;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_substCore___lambda__20___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_4, x_52, x_14, x_15, x_16, x_17, x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__21___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("argument must be an equality proof", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid equality proof, it is not of the form ", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nafter WHNF, variable expected, but obtained", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(x = t)", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__12;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__13;
x_2 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(t = x)", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__16;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__17;
x_2 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__19;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__20;
x_3 = l_Lean_Meta_substCore___lambda__21___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("substituting ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (id: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") with ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__21___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__21___closed__26;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_MVarId_getTag(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_substCore___lambda__21___closed__2;
lean_inc(x_1);
x_16 = l_Lean_MVarId_checkNotAssigned(x_1, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_2);
x_18 = l_Lean_FVarId_getDecl(x_2, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l_Lean_Meta_matchEq_x3f(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_substCore___lambda__21___closed__6;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_25, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_34 = x_29;
} else {
 lean_dec_ref(x_29);
 x_34 = lean_box(0);
}
if (x_6 == 0)
{
uint8_t x_163; 
x_163 = 0;
x_35 = x_163;
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = 1;
x_35 = x_164;
goto block_162;
}
block_162:
{
lean_object* x_36; 
if (x_35 == 0)
{
lean_inc(x_32);
x_36 = x_32;
goto block_161;
}
else
{
lean_inc(x_33);
x_36 = x_33;
goto block_161;
}
block_161:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_36, x_7, x_8, x_9, x_10, x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (x_35 == 0)
{
lean_dec(x_32);
x_41 = x_33;
goto block_160;
}
else
{
lean_dec(x_33);
x_41 = x_32;
goto block_160;
}
block_160:
{
lean_object* x_42; 
x_42 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_41, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_38) == 1)
{
uint8_t x_43; 
lean_dec(x_28);
lean_dec(x_21);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = l_Lean_Meta_substCore___lambda__21___closed__21;
x_48 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_47, x_7, x_8, x_9, x_10, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_42);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_30);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_substCore___lambda__20(x_44, x_46, x_2, x_1, x_47, x_13, x_3, x_4, x_35, x_5, x_38, x_15, x_52, x_7, x_8, x_9, x_10, x_51);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_55 = lean_ctor_get(x_48, 1);
x_56 = lean_ctor_get(x_48, 0);
lean_dec(x_56);
lean_inc(x_38);
x_57 = l_Lean_MessageData_ofExpr(x_38);
x_58 = l_Lean_Meta_substCore___lambda__21___closed__23;
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_58);
x_59 = l_Lean_Meta_substCore___lambda__21___closed__25;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_59);
lean_ctor_set(x_42, 0, x_48);
lean_inc(x_46);
x_60 = l_Lean_MessageData_ofName(x_46);
if (lean_is_scalar(x_40)) {
 x_61 = lean_alloc_ctor(7, 2, 0);
} else {
 x_61 = x_40;
 lean_ctor_set_tag(x_61, 7);
}
lean_ctor_set(x_61, 0, x_42);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_substCore___lambda__21___closed__27;
if (lean_is_scalar(x_34)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_34;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_44);
x_64 = l_Lean_MessageData_ofExpr(x_44);
if (lean_is_scalar(x_30)) {
 x_65 = lean_alloc_ctor(7, 2, 0);
} else {
 x_65 = x_30;
 lean_ctor_set_tag(x_65, 7);
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_67, x_7, x_8, x_9, x_10, x_55);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_substCore___lambda__20(x_44, x_46, x_2, x_1, x_47, x_13, x_3, x_4, x_35, x_5, x_38, x_15, x_69, x_7, x_8, x_9, x_10, x_70);
lean_dec(x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_dec(x_48);
lean_inc(x_38);
x_73 = l_Lean_MessageData_ofExpr(x_38);
x_74 = l_Lean_Meta_substCore___lambda__21___closed__23;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Meta_substCore___lambda__21___closed__25;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_76);
lean_ctor_set(x_42, 0, x_75);
lean_inc(x_46);
x_77 = l_Lean_MessageData_ofName(x_46);
if (lean_is_scalar(x_40)) {
 x_78 = lean_alloc_ctor(7, 2, 0);
} else {
 x_78 = x_40;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_42);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Meta_substCore___lambda__21___closed__27;
if (lean_is_scalar(x_34)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_34;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_44);
x_81 = l_Lean_MessageData_ofExpr(x_44);
if (lean_is_scalar(x_30)) {
 x_82 = lean_alloc_ctor(7, 2, 0);
} else {
 x_82 = x_30;
 lean_ctor_set_tag(x_82, 7);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_84, x_7, x_8, x_9, x_10, x_72);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_substCore___lambda__20(x_44, x_46, x_2, x_1, x_47, x_13, x_3, x_4, x_35, x_5, x_38, x_15, x_86, x_7, x_8, x_9, x_10, x_87);
lean_dec(x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_89 = lean_ctor_get(x_42, 0);
x_90 = lean_ctor_get(x_42, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_42);
x_91 = lean_ctor_get(x_38, 0);
lean_inc(x_91);
x_92 = l_Lean_Meta_substCore___lambda__21___closed__21;
x_93 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_92, x_7, x_8, x_9, x_10, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_30);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_box(0);
x_98 = l_Lean_Meta_substCore___lambda__20(x_89, x_91, x_2, x_1, x_92, x_13, x_3, x_4, x_35, x_5, x_38, x_15, x_97, x_7, x_8, x_9, x_10, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
lean_inc(x_38);
x_101 = l_Lean_MessageData_ofExpr(x_38);
x_102 = l_Lean_Meta_substCore___lambda__21___closed__23;
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_100;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Meta_substCore___lambda__21___closed__25;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_91);
x_106 = l_Lean_MessageData_ofName(x_91);
if (lean_is_scalar(x_40)) {
 x_107 = lean_alloc_ctor(7, 2, 0);
} else {
 x_107 = x_40;
 lean_ctor_set_tag(x_107, 7);
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Meta_substCore___lambda__21___closed__27;
if (lean_is_scalar(x_34)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_34;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_inc(x_89);
x_110 = l_Lean_MessageData_ofExpr(x_89);
if (lean_is_scalar(x_30)) {
 x_111 = lean_alloc_ctor(7, 2, 0);
} else {
 x_111 = x_30;
 lean_ctor_set_tag(x_111, 7);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_92, x_113, x_7, x_8, x_9, x_10, x_99);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Meta_substCore___lambda__20(x_89, x_91, x_2, x_1, x_92, x_13, x_3, x_4, x_35, x_5, x_38, x_15, x_115, x_7, x_8, x_9, x_10, x_116);
lean_dec(x_115);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_42);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_42, 1);
x_120 = lean_ctor_get(x_42, 0);
lean_dec(x_120);
x_121 = l_Lean_indentExpr(x_21);
x_122 = l_Lean_indentExpr(x_38);
if (x_35 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = l_Lean_Meta_substCore___lambda__21___closed__14;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_121);
lean_ctor_set(x_42, 0, x_123);
x_124 = l_Lean_Meta_substCore___lambda__21___closed__10;
if (lean_is_scalar(x_40)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_40;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_42);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_34)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_34;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
x_127 = l_Lean_Meta_substCore___lambda__2___closed__6;
if (lean_is_scalar(x_30)) {
 x_128 = lean_alloc_ctor(7, 2, 0);
} else {
 x_128 = x_30;
 lean_ctor_set_tag(x_128, 7);
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_28)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_28;
}
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_129, x_7, x_8, x_9, x_10, x_119);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = l_Lean_Meta_substCore___lambda__21___closed__18;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_121);
lean_ctor_set(x_42, 0, x_131);
x_132 = l_Lean_Meta_substCore___lambda__21___closed__10;
if (lean_is_scalar(x_40)) {
 x_133 = lean_alloc_ctor(7, 2, 0);
} else {
 x_133 = x_40;
 lean_ctor_set_tag(x_133, 7);
}
lean_ctor_set(x_133, 0, x_42);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_34)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_34;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_122);
x_135 = l_Lean_Meta_substCore___lambda__2___closed__6;
if (lean_is_scalar(x_30)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_30;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_28)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_28;
}
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_137, x_7, x_8, x_9, x_10, x_119);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_42, 1);
lean_inc(x_139);
lean_dec(x_42);
x_140 = l_Lean_indentExpr(x_21);
x_141 = l_Lean_indentExpr(x_38);
if (x_35 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_142 = l_Lean_Meta_substCore___lambda__21___closed__14;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
x_144 = l_Lean_Meta_substCore___lambda__21___closed__10;
if (lean_is_scalar(x_40)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_40;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_34)) {
 x_146 = lean_alloc_ctor(7, 2, 0);
} else {
 x_146 = x_34;
 lean_ctor_set_tag(x_146, 7);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
x_147 = l_Lean_Meta_substCore___lambda__2___closed__6;
if (lean_is_scalar(x_30)) {
 x_148 = lean_alloc_ctor(7, 2, 0);
} else {
 x_148 = x_30;
 lean_ctor_set_tag(x_148, 7);
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_28)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_28;
}
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_149, x_7, x_8, x_9, x_10, x_139);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = l_Lean_Meta_substCore___lambda__21___closed__18;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_140);
x_153 = l_Lean_Meta_substCore___lambda__21___closed__10;
if (lean_is_scalar(x_40)) {
 x_154 = lean_alloc_ctor(7, 2, 0);
} else {
 x_154 = x_40;
 lean_ctor_set_tag(x_154, 7);
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_34)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_34;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_141);
x_156 = l_Lean_Meta_substCore___lambda__2___closed__6;
if (lean_is_scalar(x_30)) {
 x_157 = lean_alloc_ctor(7, 2, 0);
} else {
 x_157 = x_30;
 lean_ctor_set_tag(x_157, 7);
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
if (lean_is_scalar(x_28)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_28;
}
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_158, x_7, x_8, x_9, x_10, x_139);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_159;
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
uint8_t x_165; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_22);
if (x_165 == 0)
{
return x_22;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_22, 0);
x_167 = lean_ctor_get(x_22, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_22);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_18);
if (x_169 == 0)
{
return x_18;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_18, 0);
x_171 = lean_ctor_get(x_18, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_18);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_16);
if (x_173 == 0)
{
return x_16;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_16, 0);
x_175 = lean_ctor_get(x_16, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_16);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_12);
if (x_177 == 0)
{
return x_12;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_12, 0);
x_179 = lean_ctor_get(x_12, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_12);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_5);
x_13 = lean_box(x_6);
x_14 = lean_box(x_3);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__21___boxed), 11, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
x_16 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_substCore___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object** _args) {
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
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object** _args) {
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
x_23 = lean_unbox(x_8);
lean_dec(x_8);
x_24 = l_Lean_Meta_substCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_4);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_substCore___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_substCore___lambda__6(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lean_Meta_substCore___lambda__7(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object** _args) {
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
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = l_Lean_Meta_substCore___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object** _args) {
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
x_23 = lean_unbox(x_8);
lean_dec(x_8);
x_24 = l_Lean_Meta_substCore___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_4);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_substCore___lambda__10(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lean_Meta_substCore___lambda__11(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object** _args) {
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
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = l_Lean_Meta_substCore___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object** _args) {
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
x_23 = lean_unbox(x_8);
lean_dec(x_8);
x_24 = l_Lean_Meta_substCore___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_4);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__14___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l_Lean_Meta_substCore___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__15___boxed(lean_object** _args) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = lean_unbox(x_14);
lean_dec(x_14);
x_23 = lean_unbox(x_15);
lean_dec(x_15);
x_24 = l_Lean_Meta_substCore___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_22, x_23, x_16, x_17, x_18, x_19, x_20);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__16___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_11);
lean_dec(x_11);
x_21 = lean_unbox(x_12);
lean_dec(x_12);
x_22 = l_Lean_Meta_substCore___lambda__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_20, x_21, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__17___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_11);
lean_dec(x_11);
x_21 = lean_unbox(x_12);
lean_dec(x_12);
x_22 = l_Lean_Meta_substCore___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_20, x_21, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__18___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_10);
lean_dec(x_10);
x_20 = lean_unbox(x_11);
lean_dec(x_11);
x_21 = l_Lean_Meta_substCore___lambda__18(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_8, x_9, x_19, x_20, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l_Lean_Meta_substCore___lambda__19(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__20___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = lean_unbox(x_10);
lean_dec(x_10);
x_22 = l_Lean_Meta_substCore___lambda__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_20, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_substCore___lambda__21(x_1, x_2, x_3, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_substCore(x_1, x_2, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Meta_intro1Core(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
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
static lean_object* _init_l_Lean_Meta_heqToEq___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_heqToEq___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_heqToEq___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_heqToEq___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_whnf(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Meta_heqToEq___lambda__2___closed__2;
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_13);
x_21 = l_Lean_Expr_appFn_x21(x_15);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_27 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEq(x_24, x_26, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
lean_inc(x_1);
x_38 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Lean_Meta_mkEqOfHEq(x_38, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Lean_Meta_mkEq(x_25, x_27, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_LocalDecl_userName(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_46 = l_Lean_MVarId_assert(x_2, x_45, x_43, x_40, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_heqToEq___lambda__2___closed__3;
if (x_3 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_apply_7(x_49, x_47, x_50, x_4, x_5, x_6, x_7, x_48);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_MVarId_tryClear(x_47, x_1, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = lean_apply_7(x_49, x_53, x_55, x_4, x_5, x_6, x_7, x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_46);
if (x_61 == 0)
{
return x_46;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_46, 0);
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_46);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_42);
if (x_65 == 0)
{
return x_42;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_42, 0);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_42);
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
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_39);
if (x_69 == 0)
{
return x_39;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_39, 0);
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_39);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_28);
if (x_73 == 0)
{
return x_28;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_28, 0);
x_75 = lean_ctor_get(x_28, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_28);
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
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_13, 0);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_13);
x_79 = l_Lean_Meta_heqToEq___lambda__2___closed__2;
x_80 = lean_unsigned_to_nat(4u);
x_81 = l_Lean_Expr_isAppOfArity(x_77, x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = l_Lean_Expr_appFn_x21(x_77);
x_85 = l_Lean_Expr_appFn_x21(x_84);
x_86 = l_Lean_Expr_appFn_x21(x_85);
x_87 = l_Lean_Expr_appArg_x21(x_86);
lean_dec(x_86);
x_88 = l_Lean_Expr_appArg_x21(x_85);
lean_dec(x_85);
x_89 = l_Lean_Expr_appArg_x21(x_84);
lean_dec(x_84);
x_90 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_91 = l_Lean_Meta_isExprDefEq(x_87, x_89, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_2);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
lean_inc(x_1);
x_99 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_100 = l_Lean_Meta_mkEqOfHEq(x_99, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_103 = l_Lean_Meta_mkEq(x_88, x_90, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_LocalDecl_userName(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_107 = l_Lean_MVarId_assert(x_2, x_106, x_104, x_101, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_heqToEq___lambda__2___closed__3;
if (x_3 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = lean_box(0);
x_112 = lean_apply_7(x_110, x_108, x_111, x_4, x_5, x_6, x_7, x_109);
return x_112;
}
else
{
lean_object* x_113; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l_Lean_MVarId_tryClear(x_108, x_1, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_box(0);
x_117 = lean_apply_7(x_110, x_114, x_116, x_4, x_5, x_6, x_7, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_122 = lean_ctor_get(x_107, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_107, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_124 = x_107;
} else {
 lean_dec_ref(x_107);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_103, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_128 = x_103;
} else {
 lean_dec_ref(x_103);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_100, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_100, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_132 = x_100;
} else {
 lean_dec_ref(x_100);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_91, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_91, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_136 = x_91;
} else {
 lean_dec_ref(x_91);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_13);
if (x_138 == 0)
{
return x_13;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_13, 0);
x_140 = lean_ctor_get(x_13, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_13);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_9);
if (x_142 == 0)
{
return x_9;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_9, 0);
x_144 = lean_ctor_get(x_9, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_9);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lambda__2___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_heqToEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_heqToEq___lambda__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_heqToEq(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
lean_inc(x_2);
{
size_t _tmp_4 = x_19;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_17;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1;
x_12 = l_Lean_Expr_isFVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_6(x_11, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_fvarId_x21(x_1);
x_16 = lean_name_eq(x_15, x_2);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_6(x_11, x_17, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_3, x_2, x_6, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = l_Lean_LocalDecl_fvarId(x_4);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lean_LocalDecl_fvarId(x_4);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_box(0);
x_38 = lean_apply_6(x_11, x_37, x_6, x_7, x_8, x_9, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_24 = x_39;
x_25 = x_11;
goto block_38;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
lean_dec(x_14);
x_41 = l_Lean_LocalDecl_isImplementationDetail(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_LocalDecl_type(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_43 = l_Lean_Meta_matchEq_x3f(x_42, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_24 = x_46;
x_25 = x_45;
goto block_38;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
x_54 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_52, x_7, x_8, x_9, x_10, x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_53, x_7, x_8, x_9, x_10, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_isFVar(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_free_object(x_49);
lean_free_object(x_44);
x_61 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_61, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_24 = x_63;
x_25 = x_64;
goto block_38;
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Expr_fvarId_x21(x_58);
x_70 = lean_name_eq(x_69, x_1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_49);
lean_free_object(x_44);
x_71 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_71, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_24 = x_73;
x_25 = x_74;
goto block_38;
}
else
{
uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_inc(x_55);
x_79 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_55, x_1, x_7, x_8, x_9, x_10, x_59);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
lean_dec(x_58);
lean_dec(x_55);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_84 = 1;
x_85 = lean_box(x_84);
lean_ctor_set(x_49, 1, x_85);
lean_ctor_set(x_49, 0, x_83);
lean_ctor_set(x_44, 0, x_49);
x_24 = x_44;
x_25 = x_82;
goto block_38;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_free_object(x_49);
lean_free_object(x_44);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_87, x_7, x_8, x_9, x_10, x_86);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_24 = x_89;
x_25 = x_90;
goto block_38;
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
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
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_ctor_get(x_49, 0);
x_96 = lean_ctor_get(x_49, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_49);
x_97 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_95, x_7, x_8, x_9, x_10, x_50);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_96, x_7, x_8, x_9, x_10, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_isFVar(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_free_object(x_44);
x_104 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_104, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_24 = x_106;
x_25 = x_107;
goto block_38;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Expr_fvarId_x21(x_101);
x_113 = lean_name_eq(x_112, x_1);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_free_object(x_44);
x_114 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_115 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_114, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_24 = x_116;
x_25 = x_117;
goto block_38;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_inc(x_98);
x_122 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_98, x_1, x_7, x_8, x_9, x_10, x_102);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_98);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_127 = 1;
x_128 = lean_box(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_44, 0, x_129);
x_24 = x_44;
x_25 = x_125;
goto block_38;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_44);
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
lean_dec(x_122);
x_131 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_131, x_7, x_8, x_9, x_10, x_130);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_24 = x_133;
x_25 = x_134;
goto block_38;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_139 = lean_ctor_get(x_44, 0);
lean_inc(x_139);
lean_dec(x_44);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get(x_43, 1);
lean_inc(x_141);
lean_dec(x_43);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_144 = x_140;
} else {
 lean_dec_ref(x_140);
 x_144 = lean_box(0);
}
x_145 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_142, x_7, x_8, x_9, x_10, x_141);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_143, x_7, x_8, x_9, x_10, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Expr_isFVar(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_144);
x_152 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_153 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_152, x_7, x_8, x_9, x_10, x_150);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_24 = x_154;
x_25 = x_155;
goto block_38;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = l_Lean_Expr_fvarId_x21(x_149);
x_161 = lean_name_eq(x_160, x_1);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_144);
x_162 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_163 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_162, x_7, x_8, x_9, x_10, x_150);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_24 = x_164;
x_25 = x_165;
goto block_38;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_inc(x_146);
x_170 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_146, x_1, x_7, x_8, x_9, x_10, x_150);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_149);
lean_dec(x_146);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_175 = 1;
x_176 = lean_box(x_175);
if (lean_is_scalar(x_144)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_144;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_24 = x_178;
x_25 = x_173;
goto block_38;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_144);
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_dec(x_170);
x_180 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_181 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_180, x_7, x_8, x_9, x_10, x_179);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_24 = x_182;
x_25 = x_183;
goto block_38;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_43);
if (x_188 == 0)
{
return x_43;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_43, 0);
x_190 = lean_ctor_get(x_43, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_43);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; 
lean_dec(x_40);
x_192 = lean_box(0);
x_24 = x_192;
x_25 = x_11;
goto block_38;
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_11 = x_16;
goto _start;
}
}
block_38:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; 
lean_inc(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_15 = x_26;
x_16 = x_25;
goto block_23;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_15 = x_31;
x_16 = x_25;
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_15 = x_37;
x_16 = x_25;
goto block_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_box(0);
x_10 = lean_array_size(x_8);
x_11 = 0;
x_12 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1;
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4(x_1, x_12, x_8, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_box(0);
x_32 = lean_array_size(x_30);
x_33 = 0;
x_34 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5(x_1, x_34, x_30, x_32, x_33, x_34, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_24 = x_39;
x_25 = x_11;
goto block_38;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
lean_dec(x_14);
x_41 = l_Lean_LocalDecl_isImplementationDetail(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_LocalDecl_type(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_43 = l_Lean_Meta_matchEq_x3f(x_42, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_24 = x_46;
x_25 = x_45;
goto block_38;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
x_54 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_52, x_7, x_8, x_9, x_10, x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_53, x_7, x_8, x_9, x_10, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_isFVar(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_free_object(x_49);
lean_free_object(x_44);
x_61 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_61, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_24 = x_63;
x_25 = x_64;
goto block_38;
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Expr_fvarId_x21(x_58);
x_70 = lean_name_eq(x_69, x_1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_49);
lean_free_object(x_44);
x_71 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_71, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_24 = x_73;
x_25 = x_74;
goto block_38;
}
else
{
uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_inc(x_55);
x_79 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_55, x_1, x_7, x_8, x_9, x_10, x_59);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
lean_dec(x_58);
lean_dec(x_55);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_84 = 1;
x_85 = lean_box(x_84);
lean_ctor_set(x_49, 1, x_85);
lean_ctor_set(x_49, 0, x_83);
lean_ctor_set(x_44, 0, x_49);
x_24 = x_44;
x_25 = x_82;
goto block_38;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_free_object(x_49);
lean_free_object(x_44);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_55, x_1, x_58, x_40, x_87, x_7, x_8, x_9, x_10, x_86);
lean_dec(x_40);
lean_dec(x_55);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_24 = x_89;
x_25 = x_90;
goto block_38;
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
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
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_ctor_get(x_49, 0);
x_96 = lean_ctor_get(x_49, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_49);
x_97 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_95, x_7, x_8, x_9, x_10, x_50);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_96, x_7, x_8, x_9, x_10, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_isFVar(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_free_object(x_44);
x_104 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_104, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_24 = x_106;
x_25 = x_107;
goto block_38;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Expr_fvarId_x21(x_101);
x_113 = lean_name_eq(x_112, x_1);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_free_object(x_44);
x_114 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_115 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_114, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_24 = x_116;
x_25 = x_117;
goto block_38;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_inc(x_98);
x_122 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_98, x_1, x_7, x_8, x_9, x_10, x_102);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_98);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_127 = 1;
x_128 = lean_box(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_44, 0, x_129);
x_24 = x_44;
x_25 = x_125;
goto block_38;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_44);
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
lean_dec(x_122);
x_131 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_98, x_1, x_101, x_40, x_131, x_7, x_8, x_9, x_10, x_130);
lean_dec(x_40);
lean_dec(x_98);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_24 = x_133;
x_25 = x_134;
goto block_38;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_139 = lean_ctor_get(x_44, 0);
lean_inc(x_139);
lean_dec(x_44);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get(x_43, 1);
lean_inc(x_141);
lean_dec(x_43);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_144 = x_140;
} else {
 lean_dec_ref(x_140);
 x_144 = lean_box(0);
}
x_145 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_142, x_7, x_8, x_9, x_10, x_141);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_143, x_7, x_8, x_9, x_10, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Expr_isFVar(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_144);
x_152 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_153 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_152, x_7, x_8, x_9, x_10, x_150);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_24 = x_154;
x_25 = x_155;
goto block_38;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = l_Lean_Expr_fvarId_x21(x_149);
x_161 = lean_name_eq(x_160, x_1);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_144);
x_162 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_163 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_162, x_7, x_8, x_9, x_10, x_150);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_24 = x_164;
x_25 = x_165;
goto block_38;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_inc(x_146);
x_170 = l_Lean_exprDependsOn___at_Lean_MVarId_clear___spec__7(x_146, x_1, x_7, x_8, x_9, x_10, x_150);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_149);
lean_dec(x_146);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_175 = 1;
x_176 = lean_box(x_175);
if (lean_is_scalar(x_144)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_144;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_24 = x_178;
x_25 = x_173;
goto block_38;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_144);
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_dec(x_170);
x_180 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_181 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_146, x_1, x_149, x_40, x_180, x_7, x_8, x_9, x_10, x_179);
lean_dec(x_40);
lean_dec(x_146);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_24 = x_182;
x_25 = x_183;
goto block_38;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_43);
if (x_188 == 0)
{
return x_43;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_43, 0);
x_190 = lean_ctor_get(x_43, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_43);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; 
lean_dec(x_40);
x_192 = lean_box(0);
x_24 = x_192;
x_25 = x_11;
goto block_38;
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_11 = x_16;
goto _start;
}
}
block_38:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; 
lean_inc(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_15 = x_26;
x_16 = x_25;
goto block_23;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_15 = x_31;
x_16 = x_25;
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_15 = x_37;
x_16 = x_25;
goto block_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6(x_1, x_16, x_12, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_9, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_9, 0, x_38);
return x_9;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find equation for eliminating '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_MessageData_ofExpr(x_13);
x_15 = l_Lean_Meta_substVar___lambda__1___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_substCore___lambda__20___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_21 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_2, x_19, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = 1;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
x_29 = l_Lean_Meta_substCore(x_2, x_24, x_28, x_26, x_27, x_27, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable '", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a let-declaration", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_isLet(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_substVar___lambda__1(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = l_Lean_Expr_fvar___override(x_1);
x_15 = l_Lean_MessageData_ofExpr(x_14);
x_16 = l_Lean_Meta_substVar___lambda__2___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_substVar___lambda__2___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_21, x_2, x_20, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__4(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__6(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeM_x3f___at_Lean_Meta_substVar___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_substVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_substCore___spec__4___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.subst.substEq", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lambda__14___closed__3;
x_2 = l_Lean_Meta_subst_substEq___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(187u);
x_4 = lean_unsigned_to_nat(55u);
x_5 = l_Lean_Meta_substCore___lambda__14___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid equality proof, it is not of the form (x = t) or (t = x)", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst_substEq___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_type(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Meta_matchEq_x3f(x_11, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_subst_substEq___lambda__1___closed__2;
x_16 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_15, x_3, x_4, x_5, x_6, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_25);
x_26 = lean_whnf(x_25, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_isFVar(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_24);
x_30 = lean_whnf(x_24, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_isFVar(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_1);
x_34 = l_Lean_indentExpr(x_11);
x_35 = l_Lean_Meta_subst_substEq___lambda__1___closed__4;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_34);
lean_ctor_set(x_20, 0, x_35);
x_36 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_36);
lean_ctor_set(x_18, 0, x_20);
x_37 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_37, x_2, x_13, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_free_object(x_20);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
x_39 = lean_expr_eqv(x_24, x_31);
lean_dec(x_24);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Meta_mkEq(x_31, x_25, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_44 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_MVarId_assert(x_2, x_43, x_41, x_44, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_intro1Core(x_46, x_48, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_MVarId_clear(x_53, x_1, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = 0;
x_59 = l_Lean_Meta_substCore(x_55, x_52, x_58, x_57, x_48, x_48, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
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
lean_dec(x_52);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
return x_54;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_54, 0);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_54);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_49);
if (x_75 == 0)
{
return x_49;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_49, 0);
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_49);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_45);
if (x_79 == 0)
{
return x_45;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_45, 0);
x_81 = lean_ctor_get(x_45, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_45);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_40);
if (x_83 == 0)
{
return x_40;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_40, 0);
x_85 = lean_ctor_get(x_40, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_40);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_9);
x_87 = lean_box(0);
x_88 = 0;
x_89 = 1;
x_90 = l_Lean_Meta_substCore(x_2, x_1, x_88, x_87, x_89, x_89, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_90);
if (x_98 == 0)
{
return x_90;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
else
{
uint8_t x_102; 
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_30);
if (x_102 == 0)
{
return x_30;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_30, 0);
x_104 = lean_ctor_get(x_30, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_30);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_20);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
x_106 = lean_expr_eqv(x_25, x_27);
lean_dec(x_25);
if (x_106 == 0)
{
lean_object* x_107; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_mkEq(x_24, x_27, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_111 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_112 = l_Lean_MVarId_assert(x_2, x_110, x_108, x_111, x_3, x_4, x_5, x_6, x_109);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_116 = l_Lean_Meta_intro1Core(x_113, x_115, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_MVarId_clear(x_120, x_1, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
x_125 = l_Lean_Meta_substCore(x_122, x_119, x_115, x_124, x_115, x_115, x_3, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
lean_ctor_set(x_125, 0, x_128);
return x_125;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_125, 0);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_125);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_125);
if (x_133 == 0)
{
return x_125;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_125, 0);
x_135 = lean_ctor_get(x_125, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_125);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_119);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = !lean_is_exclusive(x_121);
if (x_137 == 0)
{
return x_121;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_121, 0);
x_139 = lean_ctor_get(x_121, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_121);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_116);
if (x_141 == 0)
{
return x_116;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_116, 0);
x_143 = lean_ctor_get(x_116, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_116);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_112);
if (x_145 == 0)
{
return x_112;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_112, 0);
x_147 = lean_ctor_get(x_112, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_112);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_107);
if (x_149 == 0)
{
return x_107;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_107, 0);
x_151 = lean_ctor_get(x_107, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_107);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
x_153 = lean_box(0);
x_154 = 1;
x_155 = l_Lean_Meta_substCore(x_2, x_1, x_154, x_153, x_154, x_154, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
lean_ctor_set(x_155, 0, x_158);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_155);
if (x_163 == 0)
{
return x_155;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_155, 0);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_155);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_26);
if (x_167 == 0)
{
return x_26;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_26, 0);
x_169 = lean_ctor_get(x_26, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_26);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_20, 0);
x_172 = lean_ctor_get(x_20, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_172);
x_173 = lean_whnf(x_172, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Expr_isFVar(x_174);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_174);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_171);
x_177 = lean_whnf(x_171, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Expr_isFVar(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_178);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_9);
lean_dec(x_1);
x_181 = l_Lean_indentExpr(x_11);
x_182 = l_Lean_Meta_subst_substEq___lambda__1___closed__4;
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = l_Lean_Meta_substCore___lambda__2___closed__6;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_184);
lean_ctor_set(x_18, 0, x_183);
x_185 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_186 = l_Lean_Meta_throwTacticEx___rarg(x_185, x_2, x_13, x_3, x_4, x_5, x_6, x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_186;
}
else
{
uint8_t x_187; 
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
x_187 = lean_expr_eqv(x_171, x_178);
lean_dec(x_171);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_188 = l_Lean_Meta_mkEq(x_178, x_172, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_192 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_193 = l_Lean_MVarId_assert(x_2, x_191, x_189, x_192, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_197 = l_Lean_Meta_intro1Core(x_194, x_196, x_3, x_4, x_5, x_6, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_202 = l_Lean_MVarId_clear(x_201, x_1, x_3, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_box(0);
x_206 = 0;
x_207 = l_Lean_Meta_substCore(x_203, x_200, x_206, x_205, x_196, x_196, x_3, x_4, x_5, x_6, x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_215 = x_207;
} else {
 lean_dec_ref(x_207);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_ctor_get(x_202, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_219 = x_202;
} else {
 lean_dec_ref(x_202);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_221 = lean_ctor_get(x_197, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_197, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_223 = x_197;
} else {
 lean_dec_ref(x_197);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_225 = lean_ctor_get(x_193, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_193, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_227 = x_193;
} else {
 lean_dec_ref(x_193);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = lean_ctor_get(x_188, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_188, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_231 = x_188;
} else {
 lean_dec_ref(x_188);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_object* x_233; uint8_t x_234; uint8_t x_235; lean_object* x_236; 
lean_dec(x_178);
lean_dec(x_172);
lean_dec(x_9);
x_233 = lean_box(0);
x_234 = 0;
x_235 = 1;
x_236 = l_Lean_Meta_substCore(x_2, x_1, x_234, x_233, x_235, x_235, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_238);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_244 = x_236;
} else {
 lean_dec_ref(x_236);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_172);
lean_dec(x_171);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_177, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_177, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_248 = x_177;
} else {
 lean_dec_ref(x_177);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
uint8_t x_250; 
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
x_250 = lean_expr_eqv(x_172, x_174);
lean_dec(x_172);
if (x_250 == 0)
{
lean_object* x_251; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_251 = l_Lean_Meta_mkEq(x_171, x_174, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_255 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_256 = l_Lean_MVarId_assert(x_2, x_254, x_252, x_255, x_3, x_4, x_5, x_6, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_260 = l_Lean_Meta_intro1Core(x_257, x_259, x_3, x_4, x_5, x_6, x_258);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_265 = l_Lean_MVarId_clear(x_264, x_1, x_3, x_4, x_5, x_6, x_262);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_box(0);
x_269 = l_Lean_Meta_substCore(x_266, x_263, x_259, x_268, x_259, x_259, x_3, x_4, x_5, x_6, x_267);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_271);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_269, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_269, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_277 = x_269;
} else {
 lean_dec_ref(x_269);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_263);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_279 = lean_ctor_get(x_265, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_265, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_281 = x_265;
} else {
 lean_dec_ref(x_265);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_283 = lean_ctor_get(x_260, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_260, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_285 = x_260;
} else {
 lean_dec_ref(x_260);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_287 = lean_ctor_get(x_256, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_256, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_289 = x_256;
} else {
 lean_dec_ref(x_256);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_ctor_get(x_251, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_251, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_293 = x_251;
} else {
 lean_dec_ref(x_251);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; uint8_t x_296; lean_object* x_297; 
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_9);
x_295 = lean_box(0);
x_296 = 1;
x_297 = l_Lean_Meta_substCore(x_2, x_1, x_296, x_295, x_296, x_296, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_299);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_297, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_297, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_305 = x_297;
} else {
 lean_dec_ref(x_297);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_172);
lean_dec(x_171);
lean_free_object(x_18);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_307 = lean_ctor_get(x_173, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_173, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_309 = x_173;
} else {
 lean_dec_ref(x_173);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_311 = lean_ctor_get(x_18, 1);
lean_inc(x_311);
lean_dec(x_18);
x_312 = lean_ctor_get(x_12, 1);
lean_inc(x_312);
lean_dec(x_12);
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_315 = x_311;
} else {
 lean_dec_ref(x_311);
 x_315 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_314);
x_316 = lean_whnf(x_314, x_3, x_4, x_5, x_6, x_312);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_Expr_isFVar(x_317);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_317);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_313);
x_320 = lean_whnf(x_313, x_3, x_4, x_5, x_6, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Lean_Expr_isFVar(x_321);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_321);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_9);
lean_dec(x_1);
x_324 = l_Lean_indentExpr(x_11);
x_325 = l_Lean_Meta_subst_substEq___lambda__1___closed__4;
if (lean_is_scalar(x_315)) {
 x_326 = lean_alloc_ctor(7, 2, 0);
} else {
 x_326 = x_315;
 lean_ctor_set_tag(x_326, 7);
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = l_Lean_Meta_substCore___lambda__2___closed__6;
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_13, 0, x_328);
x_329 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_330 = l_Lean_Meta_throwTacticEx___rarg(x_329, x_2, x_13, x_3, x_4, x_5, x_6, x_322);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_330;
}
else
{
uint8_t x_331; 
lean_dec(x_315);
lean_free_object(x_13);
lean_dec(x_11);
x_331 = lean_expr_eqv(x_313, x_321);
lean_dec(x_313);
if (x_331 == 0)
{
lean_object* x_332; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_332 = l_Lean_Meta_mkEq(x_321, x_314, x_3, x_4, x_5, x_6, x_322);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_336 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_337 = l_Lean_MVarId_assert(x_2, x_335, x_333, x_336, x_3, x_4, x_5, x_6, x_334);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_341 = l_Lean_Meta_intro1Core(x_338, x_340, x_3, x_4, x_5, x_6, x_339);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec(x_342);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_346 = l_Lean_MVarId_clear(x_345, x_1, x_3, x_4, x_5, x_6, x_343);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_box(0);
x_350 = 0;
x_351 = l_Lean_Meta_substCore(x_347, x_344, x_350, x_349, x_340, x_340, x_3, x_4, x_5, x_6, x_348);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_351, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_351, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_359 = x_351;
} else {
 lean_dec_ref(x_351);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_344);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_361 = lean_ctor_get(x_346, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_346, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_363 = x_346;
} else {
 lean_dec_ref(x_346);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_365 = lean_ctor_get(x_341, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_341, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_367 = x_341;
} else {
 lean_dec_ref(x_341);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_369 = lean_ctor_get(x_337, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_337, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_371 = x_337;
} else {
 lean_dec_ref(x_337);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_373 = lean_ctor_get(x_332, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_332, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_375 = x_332;
} else {
 lean_dec_ref(x_332);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
else
{
lean_object* x_377; uint8_t x_378; uint8_t x_379; lean_object* x_380; 
lean_dec(x_321);
lean_dec(x_314);
lean_dec(x_9);
x_377 = lean_box(0);
x_378 = 0;
x_379 = 1;
x_380 = l_Lean_Meta_substCore(x_2, x_1, x_378, x_377, x_379, x_379, x_3, x_4, x_5, x_6, x_322);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
lean_dec(x_381);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_382);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_380, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_380, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_388 = x_380;
} else {
 lean_dec_ref(x_380);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = lean_ctor_get(x_320, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_320, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_392 = x_320;
} else {
 lean_dec_ref(x_320);
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
uint8_t x_394; 
lean_dec(x_315);
lean_free_object(x_13);
lean_dec(x_11);
x_394 = lean_expr_eqv(x_314, x_317);
lean_dec(x_314);
if (x_394 == 0)
{
lean_object* x_395; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_395 = l_Lean_Meta_mkEq(x_313, x_317, x_3, x_4, x_5, x_6, x_318);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_399 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_400 = l_Lean_MVarId_assert(x_2, x_398, x_396, x_399, x_3, x_4, x_5, x_6, x_397);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_404 = l_Lean_Meta_intro1Core(x_401, x_403, x_3, x_4, x_5, x_6, x_402);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_409 = l_Lean_MVarId_clear(x_408, x_1, x_3, x_4, x_5, x_6, x_406);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_box(0);
x_413 = l_Lean_Meta_substCore(x_410, x_407, x_403, x_412, x_403, x_403, x_3, x_4, x_5, x_6, x_411);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_416 = x_413;
} else {
 lean_dec_ref(x_413);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
if (lean_is_scalar(x_416)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_416;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_415);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_413, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_413, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_421 = x_413;
} else {
 lean_dec_ref(x_413);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_407);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_423 = lean_ctor_get(x_409, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_409, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_425 = x_409;
} else {
 lean_dec_ref(x_409);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_427 = lean_ctor_get(x_404, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_404, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_429 = x_404;
} else {
 lean_dec_ref(x_404);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_431 = lean_ctor_get(x_400, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_400, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_433 = x_400;
} else {
 lean_dec_ref(x_400);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_435 = lean_ctor_get(x_395, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_395, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_437 = x_395;
} else {
 lean_dec_ref(x_395);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
else
{
lean_object* x_439; uint8_t x_440; lean_object* x_441; 
lean_dec(x_317);
lean_dec(x_313);
lean_dec(x_9);
x_439 = lean_box(0);
x_440 = 1;
x_441 = l_Lean_Meta_substCore(x_2, x_1, x_440, x_439, x_440, x_440, x_3, x_4, x_5, x_6, x_318);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_444 = x_441;
} else {
 lean_dec_ref(x_441);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_442, 1);
lean_inc(x_445);
lean_dec(x_442);
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_443);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_441, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_441, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_449 = x_441;
} else {
 lean_dec_ref(x_441);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_free_object(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_451 = lean_ctor_get(x_316, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_316, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_453 = x_316;
} else {
 lean_dec_ref(x_316);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_455 = lean_ctor_get(x_13, 0);
lean_inc(x_455);
lean_dec(x_13);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_12, 1);
lean_inc(x_458);
lean_dec(x_12);
x_459 = lean_ctor_get(x_456, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_456, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_461 = x_456;
} else {
 lean_dec_ref(x_456);
 x_461 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_460);
x_462 = lean_whnf(x_460, x_3, x_4, x_5, x_6, x_458);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = l_Lean_Expr_isFVar(x_463);
if (x_465 == 0)
{
lean_object* x_466; 
lean_dec(x_463);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_459);
x_466 = lean_whnf(x_459, x_3, x_4, x_5, x_6, x_464);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = l_Lean_Expr_isFVar(x_467);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_467);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_9);
lean_dec(x_1);
x_470 = l_Lean_indentExpr(x_11);
x_471 = l_Lean_Meta_subst_substEq___lambda__1___closed__4;
if (lean_is_scalar(x_461)) {
 x_472 = lean_alloc_ctor(7, 2, 0);
} else {
 x_472 = x_461;
 lean_ctor_set_tag(x_472, 7);
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = l_Lean_Meta_substCore___lambda__2___closed__6;
if (lean_is_scalar(x_457)) {
 x_474 = lean_alloc_ctor(7, 2, 0);
} else {
 x_474 = x_457;
 lean_ctor_set_tag(x_474, 7);
}
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_476 = l_Lean_Meta_substCore___lambda__21___closed__2;
x_477 = l_Lean_Meta_throwTacticEx___rarg(x_476, x_2, x_475, x_3, x_4, x_5, x_6, x_468);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_477;
}
else
{
uint8_t x_478; 
lean_dec(x_461);
lean_dec(x_457);
lean_dec(x_11);
x_478 = lean_expr_eqv(x_459, x_467);
lean_dec(x_459);
if (x_478 == 0)
{
lean_object* x_479; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_479 = l_Lean_Meta_mkEq(x_467, x_460, x_3, x_4, x_5, x_6, x_468);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_483 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_484 = l_Lean_MVarId_assert(x_2, x_482, x_480, x_483, x_3, x_4, x_5, x_6, x_481);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_487 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_488 = l_Lean_Meta_intro1Core(x_485, x_487, x_3, x_4, x_5, x_6, x_486);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_ctor_get(x_489, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
lean_dec(x_489);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_493 = l_Lean_MVarId_clear(x_492, x_1, x_3, x_4, x_5, x_6, x_490);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; lean_object* x_498; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_box(0);
x_497 = 0;
x_498 = l_Lean_Meta_substCore(x_494, x_491, x_497, x_496, x_487, x_487, x_3, x_4, x_5, x_6, x_495);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_501 = x_498;
} else {
 lean_dec_ref(x_498);
 x_501 = lean_box(0);
}
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
lean_dec(x_499);
if (lean_is_scalar(x_501)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_501;
}
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_500);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = lean_ctor_get(x_498, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_498, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_506 = x_498;
} else {
 lean_dec_ref(x_498);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_491);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_508 = lean_ctor_get(x_493, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_493, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_510 = x_493;
} else {
 lean_dec_ref(x_493);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_512 = lean_ctor_get(x_488, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_488, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_514 = x_488;
} else {
 lean_dec_ref(x_488);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_516 = lean_ctor_get(x_484, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_484, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_518 = x_484;
} else {
 lean_dec_ref(x_484);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_520 = lean_ctor_get(x_479, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_479, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_522 = x_479;
} else {
 lean_dec_ref(x_479);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; uint8_t x_525; uint8_t x_526; lean_object* x_527; 
lean_dec(x_467);
lean_dec(x_460);
lean_dec(x_9);
x_524 = lean_box(0);
x_525 = 0;
x_526 = 1;
x_527 = l_Lean_Meta_substCore(x_2, x_1, x_525, x_524, x_526, x_526, x_3, x_4, x_5, x_6, x_468);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_530 = x_527;
} else {
 lean_dec_ref(x_527);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
lean_dec(x_528);
if (lean_is_scalar(x_530)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_530;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_529);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_533 = lean_ctor_get(x_527, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_527, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_535 = x_527;
} else {
 lean_dec_ref(x_527);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
return x_536;
}
}
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_537 = lean_ctor_get(x_466, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_466, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_539 = x_466;
} else {
 lean_dec_ref(x_466);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
else
{
uint8_t x_541; 
lean_dec(x_461);
lean_dec(x_457);
lean_dec(x_11);
x_541 = lean_expr_eqv(x_460, x_463);
lean_dec(x_460);
if (x_541 == 0)
{
lean_object* x_542; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_542 = l_Lean_Meta_mkEq(x_459, x_463, x_3, x_4, x_5, x_6, x_464);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_546 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_547 = l_Lean_MVarId_assert(x_2, x_545, x_543, x_546, x_3, x_4, x_5, x_6, x_544);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_550 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_551 = l_Lean_Meta_intro1Core(x_548, x_550, x_3, x_4, x_5, x_6, x_549);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_552, 1);
lean_inc(x_555);
lean_dec(x_552);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_556 = l_Lean_MVarId_clear(x_555, x_1, x_3, x_4, x_5, x_6, x_553);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_box(0);
x_560 = l_Lean_Meta_substCore(x_557, x_554, x_550, x_559, x_550, x_550, x_3, x_4, x_5, x_6, x_558);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_563 = x_560;
} else {
 lean_dec_ref(x_560);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
lean_dec(x_561);
if (lean_is_scalar(x_563)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_563;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_562);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_566 = lean_ctor_get(x_560, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_560, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_568 = x_560;
} else {
 lean_dec_ref(x_560);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_554);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_570 = lean_ctor_get(x_556, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_556, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_572 = x_556;
} else {
 lean_dec_ref(x_556);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_571);
return x_573;
}
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_574 = lean_ctor_get(x_551, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_551, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_576 = x_551;
} else {
 lean_dec_ref(x_551);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_578 = lean_ctor_get(x_547, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_547, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_580 = x_547;
} else {
 lean_dec_ref(x_547);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_579);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_582 = lean_ctor_get(x_542, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_542, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_584 = x_542;
} else {
 lean_dec_ref(x_542);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
else
{
lean_object* x_586; uint8_t x_587; lean_object* x_588; 
lean_dec(x_463);
lean_dec(x_459);
lean_dec(x_9);
x_586 = lean_box(0);
x_587 = 1;
x_588 = l_Lean_Meta_substCore(x_2, x_1, x_587, x_586, x_587, x_587, x_3, x_4, x_5, x_6, x_464);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_589, 1);
lean_inc(x_592);
lean_dec(x_589);
if (lean_is_scalar(x_591)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_591;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_590);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_588, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_588, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_596 = x_588;
} else {
 lean_dec_ref(x_588);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_598 = lean_ctor_get(x_462, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_462, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_600 = x_462;
} else {
 lean_dec_ref(x_462);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
return x_601;
}
}
}
}
else
{
uint8_t x_602; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_602 = !lean_is_exclusive(x_12);
if (x_602 == 0)
{
return x_12;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_12, 0);
x_604 = lean_ctor_get(x_12, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_12);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_606 = !lean_is_exclusive(x_8);
if (x_606 == 0)
{
return x_8;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_8, 0);
x_608 = lean_ctor_get(x_8, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_8);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst_substEq___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_matchEq_x3f(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_matchHEq_x3f(x_9, x_3, x_4, x_5, x_6, x_13);
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
x_17 = l_Lean_Meta_substVar(x_2, x_1, x_3, x_4, x_5, x_6, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Lean_Meta_heqToEq(x_2, x_1, x_19, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_name_eq(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Meta_subst(x_24, x_23, x_3, x_4, x_5, x_6, x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
x_27 = l_Lean_Meta_substVar(x_2, x_1, x_3, x_4, x_5, x_6, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_9);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = l_Lean_Meta_subst_substEq(x_2, x_1, x_3, x_4, x_5, x_6, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_substVar_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_34 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_substVar), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_observing_x3f___at_Lean_Meta_substVar_x3f___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_observing_x3f___at_Lean_Meta_substVar_x3f___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_substCore_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_34 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_3);
x_13 = lean_box(x_5);
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
x_16 = l_Lean_observing_x3f___at_Lean_Meta_substCore_x3f___spec__1(x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_substCore_x3f(x_1, x_2, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_substVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_subst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(x_1, x_2, x_3, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = lean_usize_add(x_7, x_30);
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(x_1, x_2, x_3, x_16, x_37, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_7, x_48);
x_7 = x_49;
x_8 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; 
lean_inc(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_18 = x_29;
x_19 = x_12;
goto block_28;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_Meta_subst_x3f(x_1, x_32, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_15);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_2);
x_18 = x_36;
x_19 = x_35;
goto block_28;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_ctor_set(x_15, 0, x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_18 = x_41;
x_19 = x_37;
goto block_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_15, 0, x_43);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_18 = x_46;
x_19 = x_37;
goto block_28;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
x_52 = l_Lean_LocalDecl_fvarId(x_51);
lean_dec(x_51);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_53 = l_Lean_Meta_subst_x3f(x_1, x_52, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_2);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_2);
x_18 = x_56;
x_19 = x_55;
goto block_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_18 = x_64;
x_19 = x_57;
goto block_28;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_67 = x_53;
} else {
 lean_dec_ref(x_53);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_array_size(x_11);
x_15 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3(x_1, x_2, x_3, x_12, x_11, x_14, x_15, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1(x_20, x_21, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_array_size(x_33);
x_37 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4(x_1, x_2, x_34, x_33, x_36, x_37, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1(x_42, x_43, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_33; 
lean_inc(x_16);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_16);
x_18 = x_33;
x_19 = x_12;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = l_Lean_LocalDecl_fvarId(x_35);
lean_dec(x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_37 = l_Lean_Meta_subst_x3f(x_1, x_36, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_15);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_2);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_18 = x_40;
x_19 = x_39;
goto block_32;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_ctor_set(x_15, 0, x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_18 = x_45;
x_19 = x_41;
goto block_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_15, 0, x_47);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_18 = x_50;
x_19 = x_41;
goto block_32;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
lean_inc(x_55);
lean_dec(x_15);
x_56 = l_Lean_LocalDecl_fvarId(x_55);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_57 = l_Lean_Meta_subst_x3f(x_1, x_56, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_2);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_2);
x_18 = x_60;
x_19 = x_59;
goto block_32;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_18 = x_68;
x_19 = x_61;
goto block_32;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_71 = x_57;
} else {
 lean_dec_ref(x_57);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
block_32:
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_ctor_set_tag(x_18, 1);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_17;
}
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_6, x_29);
x_6 = x_30;
x_7 = x_28;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_size(x_21);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5(x_1, x_2, x_22, x_21, x_24, x_25, x_23, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1;
x_11 = l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1(x_1, x_10, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_substSomeVar_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_substSomeVar_x3f___spec__5(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at_Lean_Meta_substSomeVar_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_substSomeVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_1 = x_14;
x_6 = x_13;
goto _start;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9;
x_2 = l_Lean_Meta_substCore___lambda__21___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14;
x_2 = lean_unsigned_to_nat(3839u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_substCore___lambda__21___closed__21;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
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
l_panic___at_Lean_Meta_substCore___spec__4___closed__1 = _init_l_panic___at_Lean_Meta_substCore___spec__4___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_substCore___spec__4___closed__1);
l_Lean_Meta_substCore___lambda__2___closed__1 = _init_l_Lean_Meta_substCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__1);
l_Lean_Meta_substCore___lambda__2___closed__2 = _init_l_Lean_Meta_substCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__2);
l_Lean_Meta_substCore___lambda__2___closed__3 = _init_l_Lean_Meta_substCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__3);
l_Lean_Meta_substCore___lambda__2___closed__4 = _init_l_Lean_Meta_substCore___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__4);
l_Lean_Meta_substCore___lambda__2___closed__5 = _init_l_Lean_Meta_substCore___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__5);
l_Lean_Meta_substCore___lambda__2___closed__6 = _init_l_Lean_Meta_substCore___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__6);
l_Lean_Meta_substCore___lambda__14___closed__1 = _init_l_Lean_Meta_substCore___lambda__14___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__1);
l_Lean_Meta_substCore___lambda__14___closed__2 = _init_l_Lean_Meta_substCore___lambda__14___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__2);
l_Lean_Meta_substCore___lambda__14___closed__3 = _init_l_Lean_Meta_substCore___lambda__14___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__3);
l_Lean_Meta_substCore___lambda__14___closed__4 = _init_l_Lean_Meta_substCore___lambda__14___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__4);
l_Lean_Meta_substCore___lambda__14___closed__5 = _init_l_Lean_Meta_substCore___lambda__14___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__5);
l_Lean_Meta_substCore___lambda__14___closed__6 = _init_l_Lean_Meta_substCore___lambda__14___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__14___closed__6);
l_Lean_Meta_substCore___lambda__17___closed__1 = _init_l_Lean_Meta_substCore___lambda__17___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__17___closed__1);
l_Lean_Meta_substCore___lambda__17___closed__2 = _init_l_Lean_Meta_substCore___lambda__17___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__17___closed__2);
l_Lean_Meta_substCore___lambda__18___closed__1 = _init_l_Lean_Meta_substCore___lambda__18___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__18___closed__1);
l_Lean_Meta_substCore___lambda__18___closed__2 = _init_l_Lean_Meta_substCore___lambda__18___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__18___closed__2);
l_Lean_Meta_substCore___lambda__19___closed__1 = _init_l_Lean_Meta_substCore___lambda__19___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__19___closed__1);
l_Lean_Meta_substCore___lambda__19___closed__2 = _init_l_Lean_Meta_substCore___lambda__19___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__19___closed__2);
l_Lean_Meta_substCore___lambda__20___closed__1 = _init_l_Lean_Meta_substCore___lambda__20___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__20___closed__1);
l_Lean_Meta_substCore___lambda__20___closed__2 = _init_l_Lean_Meta_substCore___lambda__20___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__20___closed__2);
l_Lean_Meta_substCore___lambda__20___closed__3 = _init_l_Lean_Meta_substCore___lambda__20___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__20___closed__3);
l_Lean_Meta_substCore___lambda__20___closed__4 = _init_l_Lean_Meta_substCore___lambda__20___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__20___closed__4);
l_Lean_Meta_substCore___lambda__21___closed__1 = _init_l_Lean_Meta_substCore___lambda__21___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__1);
l_Lean_Meta_substCore___lambda__21___closed__2 = _init_l_Lean_Meta_substCore___lambda__21___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__2);
l_Lean_Meta_substCore___lambda__21___closed__3 = _init_l_Lean_Meta_substCore___lambda__21___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__3);
l_Lean_Meta_substCore___lambda__21___closed__4 = _init_l_Lean_Meta_substCore___lambda__21___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__4);
l_Lean_Meta_substCore___lambda__21___closed__5 = _init_l_Lean_Meta_substCore___lambda__21___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__5);
l_Lean_Meta_substCore___lambda__21___closed__6 = _init_l_Lean_Meta_substCore___lambda__21___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__6);
l_Lean_Meta_substCore___lambda__21___closed__7 = _init_l_Lean_Meta_substCore___lambda__21___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__7);
l_Lean_Meta_substCore___lambda__21___closed__8 = _init_l_Lean_Meta_substCore___lambda__21___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__8);
l_Lean_Meta_substCore___lambda__21___closed__9 = _init_l_Lean_Meta_substCore___lambda__21___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__9);
l_Lean_Meta_substCore___lambda__21___closed__10 = _init_l_Lean_Meta_substCore___lambda__21___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__10);
l_Lean_Meta_substCore___lambda__21___closed__11 = _init_l_Lean_Meta_substCore___lambda__21___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__11);
l_Lean_Meta_substCore___lambda__21___closed__12 = _init_l_Lean_Meta_substCore___lambda__21___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__12);
l_Lean_Meta_substCore___lambda__21___closed__13 = _init_l_Lean_Meta_substCore___lambda__21___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__13);
l_Lean_Meta_substCore___lambda__21___closed__14 = _init_l_Lean_Meta_substCore___lambda__21___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__14);
l_Lean_Meta_substCore___lambda__21___closed__15 = _init_l_Lean_Meta_substCore___lambda__21___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__15);
l_Lean_Meta_substCore___lambda__21___closed__16 = _init_l_Lean_Meta_substCore___lambda__21___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__16);
l_Lean_Meta_substCore___lambda__21___closed__17 = _init_l_Lean_Meta_substCore___lambda__21___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__17);
l_Lean_Meta_substCore___lambda__21___closed__18 = _init_l_Lean_Meta_substCore___lambda__21___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__18);
l_Lean_Meta_substCore___lambda__21___closed__19 = _init_l_Lean_Meta_substCore___lambda__21___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__19);
l_Lean_Meta_substCore___lambda__21___closed__20 = _init_l_Lean_Meta_substCore___lambda__21___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__20);
l_Lean_Meta_substCore___lambda__21___closed__21 = _init_l_Lean_Meta_substCore___lambda__21___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__21);
l_Lean_Meta_substCore___lambda__21___closed__22 = _init_l_Lean_Meta_substCore___lambda__21___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__22);
l_Lean_Meta_substCore___lambda__21___closed__23 = _init_l_Lean_Meta_substCore___lambda__21___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__23);
l_Lean_Meta_substCore___lambda__21___closed__24 = _init_l_Lean_Meta_substCore___lambda__21___closed__24();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__24);
l_Lean_Meta_substCore___lambda__21___closed__25 = _init_l_Lean_Meta_substCore___lambda__21___closed__25();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__25);
l_Lean_Meta_substCore___lambda__21___closed__26 = _init_l_Lean_Meta_substCore___lambda__21___closed__26();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__26);
l_Lean_Meta_substCore___lambda__21___closed__27 = _init_l_Lean_Meta_substCore___lambda__21___closed__27();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__21___closed__27);
l_Lean_Meta_heqToEq___lambda__2___closed__1 = _init_l_Lean_Meta_heqToEq___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_heqToEq___lambda__2___closed__1);
l_Lean_Meta_heqToEq___lambda__2___closed__2 = _init_l_Lean_Meta_heqToEq___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_heqToEq___lambda__2___closed__2);
l_Lean_Meta_heqToEq___lambda__2___closed__3 = _init_l_Lean_Meta_heqToEq___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_heqToEq___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_substVar___spec__5___lambda__2___closed__1);
l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1 = _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_findSomeMAux___at_Lean_Meta_substVar___spec__3___closed__1);
l_Lean_Meta_substVar___lambda__1___closed__1 = _init_l_Lean_Meta_substVar___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__1___closed__1);
l_Lean_Meta_substVar___lambda__1___closed__2 = _init_l_Lean_Meta_substVar___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__1___closed__2);
l_Lean_Meta_substVar___lambda__2___closed__1 = _init_l_Lean_Meta_substVar___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__2___closed__1);
l_Lean_Meta_substVar___lambda__2___closed__2 = _init_l_Lean_Meta_substVar___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__2___closed__2);
l_Lean_Meta_substVar___lambda__2___closed__3 = _init_l_Lean_Meta_substVar___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__2___closed__3);
l_Lean_Meta_substVar___lambda__2___closed__4 = _init_l_Lean_Meta_substVar___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_substVar___lambda__2___closed__4);
l_Lean_Meta_subst_substEq___lambda__1___closed__1 = _init_l_Lean_Meta_subst_substEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lambda__1___closed__1);
l_Lean_Meta_subst_substEq___lambda__1___closed__2 = _init_l_Lean_Meta_subst_substEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lambda__1___closed__2);
l_Lean_Meta_subst_substEq___lambda__1___closed__3 = _init_l_Lean_Meta_subst_substEq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lambda__1___closed__3);
l_Lean_Meta_subst_substEq___lambda__1___closed__4 = _init_l_Lean_Meta_subst_substEq___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lambda__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839____closed__15);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3839_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
