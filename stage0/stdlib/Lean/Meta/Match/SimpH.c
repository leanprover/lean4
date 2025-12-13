// Lean compiler output
// Module: Lean.Meta.Match.SimpH
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Contradiction
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
lean_object* l_Lean_Meta_substVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0___boxed(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2;
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5;
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2;
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___closed__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3;
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0;
static lean_object* l_Lean_Meta_Match_simpH_x3f___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Match_simpH_x3f___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_simpH_x3f___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_array_to_list(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_mkFVar(x_5);
lean_inc(x_1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_array_push(x_3, x_9);
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_8);
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
x_4 = l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_instBEqFVarId_beq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_4);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lean_instBEqFVarId_beq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_push(x_4, x_5);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_10 = lean_array_get_size(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_dec_ref(x_4);
return x_6;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_10);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(x_4, x_13, x_14, x_6);
lean_dec_ref(x_4);
return x_15;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0;
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
x_20 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
x_38 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
lean_inc_ref(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
x_46 = lean_box(0);
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
x_55 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
lean_inc_ref(x_50);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_62);
x_63 = l_ReaderT_instMonad___redArg(x_27);
x_64 = lean_box(0);
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
x_75 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
lean_inc_ref(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = lean_box(0);
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
x_94 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
lean_inc_ref(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
x_111 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
lean_inc_ref(x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_108);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_116, 0, x_107);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_117, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_115);
if (lean_is_scalar(x_104)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_104;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = l_ReaderT_instMonad___redArg(x_119);
x_121 = lean_box(0);
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
x_132 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
lean_inc_ref(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
x_150 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
lean_inc_ref(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = lean_box(0);
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_163;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Match.SimpH", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Match.SimpH.0.Lean.Meta.Match.SimpH.substRHS", 63, 63);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ( __do_lift._@.Lean.Meta.Match.SimpH.2345676235._hygCtx._hyg.11.0 ).xs.contains rhs\n  ", 107, 107);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(46u);
x_4 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1;
x_5 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3;
x_13 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = 0;
x_18 = l_Lean_Meta_substCore(x_15, x_1, x_11, x_16, x_11, x_17, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 2);
x_27 = lean_ctor_get(x_23, 3);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
lean_inc(x_25);
x_30 = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(x_25, x_2, x_25, x_29);
lean_dec(x_25);
lean_inc(x_21);
x_31 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_30);
lean_inc(x_21);
x_32 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_26);
x_33 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_27);
lean_ctor_set(x_23, 3, x_33);
lean_ctor_set(x_23, 2, x_32);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_23, 0, x_22);
x_34 = lean_st_ref_set(x_3, x_23);
lean_dec(x_3);
x_35 = lean_box(0);
lean_ctor_set(x_18, 0, x_35);
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_39 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
lean_inc(x_36);
x_40 = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(x_36, x_2, x_36, x_39);
lean_dec(x_36);
lean_inc(x_21);
x_41 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_40);
lean_inc(x_21);
x_42 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_37);
x_43 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_21, x_38);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_st_ref_set(x_3, x_44);
lean_dec(x_3);
x_46 = lean_box(0);
lean_ctor_set(x_18, 0, x_46);
return x_18;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_take(x_3);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
lean_inc(x_51);
x_56 = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(x_51, x_2, x_51, x_55);
lean_dec(x_51);
lean_inc(x_48);
x_57 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_48, x_56);
lean_inc(x_48);
x_58 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_48, x_52);
x_59 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(x_48, x_53);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 4, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_st_ref_set(x_3, x_60);
lean_dec(x_3);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
lean_dec(x_18);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_List_isEmpty___redArg(x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0;
x_8 = l_Lean_MVarId_contradictionCore(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_substVars(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(5u);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_9);
x_12 = l_Lean_Meta_injections(x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Lean_instBEqMVarId_beq(x_17, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
x_20 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_17, x_18, x_3, x_4, x_5, x_6);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(x_9, x_3, x_4, x_5, x_6);
return x_21;
}
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = l_Lean_instBEqMVarId_beq(x_26, x_9);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_9);
x_29 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_26, x_27, x_3, x_4, x_5, x_6);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
x_30 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(x_9, x_3, x_4, x_5, x_6);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_27 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_27);
x_30 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_28);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_21 = x_30;
x_22 = x_35;
x_23 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_21 = x_37;
x_22 = x_36;
x_23 = lean_box(0);
goto block_26;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_27;
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
x_21 = x_27;
x_22 = x_38;
x_23 = lean_box(0);
goto block_26;
}
block_20:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_9);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
block_26:
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isInterrupt(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc_ref(x_22);
x_25 = l_Lean_Exception_isRuntime(x_22);
x_9 = x_22;
x_10 = x_21;
x_11 = lean_box(0);
x_12 = x_25;
goto block_20;
}
else
{
x_9 = x_22;
x_10 = x_21;
x_11 = lean_box(0);
x_12 = x_24;
goto block_20;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
return x_7;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_111; uint8_t x_112; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_111 = lean_st_ref_take(x_5);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_111, 2);
lean_dec(x_113);
lean_ctor_set(x_111, 2, x_12);
x_114 = lean_st_ref_set(x_5, x_111);
lean_inc(x_11);
x_115 = l_Lean_mkFVar(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_116 = lean_infer_type(x_115, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_218; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_117);
x_218 = l_Lean_Meta_matchEq_x3f(x_117, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
if (lean_obj_tag(x_219) == 1)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_239; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_222);
x_239 = l_Lean_Meta_isConstructorApp_x3f(x_222, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_223);
x_241 = l_Lean_Meta_isConstructorApp_x3f(x_223, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_241, 0);
if (lean_obj_tag(x_240) == 1)
{
if (lean_obj_tag(x_243) == 1)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_256 = lean_ctor_get(x_240, 0);
lean_inc(x_256);
lean_dec_ref(x_240);
x_257 = lean_ctor_get(x_256, 0);
lean_inc_ref(x_257);
lean_dec(x_256);
x_258 = lean_ctor_get(x_243, 0);
lean_inc(x_258);
lean_dec_ref(x_243);
x_259 = lean_ctor_get(x_258, 0);
lean_inc_ref(x_259);
lean_dec(x_258);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
lean_dec_ref(x_257);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = lean_name_eq(x_260, x_261);
lean_dec(x_261);
lean_dec(x_260);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_263 = lean_box(x_262);
lean_ctor_set(x_241, 0, x_263);
return x_241;
}
else
{
lean_free_object(x_241);
x_244 = x_5;
x_245 = x_6;
x_246 = x_7;
x_247 = x_8;
x_248 = x_9;
goto block_255;
}
}
else
{
lean_free_object(x_241);
lean_dec(x_243);
lean_dec_ref(x_240);
x_244 = x_5;
x_245 = x_6;
x_246 = x_7;
x_247 = x_8;
x_248 = x_9;
goto block_255;
}
}
else
{
lean_free_object(x_241);
lean_dec(x_243);
lean_dec(x_240);
x_244 = x_5;
x_245 = x_6;
x_246 = x_7;
x_247 = x_8;
x_248 = x_9;
goto block_255;
}
block_255:
{
lean_object* x_249; 
lean_inc(x_248);
lean_inc_ref(x_247);
lean_inc(x_246);
lean_inc_ref(x_245);
lean_inc(x_223);
x_249 = l_Lean_Meta_isExprDefEq(x_222, x_223, x_245, x_246, x_247, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
uint8_t x_252; 
lean_dec_ref(x_249);
x_252 = l_Lean_Expr_isFVar(x_223);
if (x_252 == 0)
{
x_224 = x_245;
x_225 = x_248;
x_226 = lean_box(0);
x_227 = x_247;
x_228 = x_246;
x_229 = x_244;
x_230 = x_252;
goto block_238;
}
else
{
lean_object* x_253; uint8_t x_254; 
x_253 = l_Lean_Expr_fvarId_x21(x_223);
x_254 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_253, x_4);
lean_dec(x_253);
x_224 = x_245;
x_225 = x_248;
x_226 = lean_box(0);
x_227 = x_247;
x_228 = x_246;
x_229 = x_244;
x_230 = x_254;
goto block_238;
}
}
else
{
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_223);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_249;
}
}
else
{
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_223);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_249;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_ctor_get(x_241, 0);
lean_inc(x_264);
lean_dec(x_241);
if (lean_obj_tag(x_240) == 1)
{
if (lean_obj_tag(x_264) == 1)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_277 = lean_ctor_get(x_240, 0);
lean_inc(x_277);
lean_dec_ref(x_240);
x_278 = lean_ctor_get(x_277, 0);
lean_inc_ref(x_278);
lean_dec(x_277);
x_279 = lean_ctor_get(x_264, 0);
lean_inc(x_279);
lean_dec_ref(x_264);
x_280 = lean_ctor_get(x_279, 0);
lean_inc_ref(x_280);
lean_dec(x_279);
x_281 = lean_ctor_get(x_278, 0);
lean_inc(x_281);
lean_dec_ref(x_278);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
lean_dec_ref(x_280);
x_283 = lean_name_eq(x_281, x_282);
lean_dec(x_282);
lean_dec(x_281);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_284 = lean_box(x_283);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
else
{
x_265 = x_5;
x_266 = x_6;
x_267 = x_7;
x_268 = x_8;
x_269 = x_9;
goto block_276;
}
}
else
{
lean_dec(x_264);
lean_dec_ref(x_240);
x_265 = x_5;
x_266 = x_6;
x_267 = x_7;
x_268 = x_8;
x_269 = x_9;
goto block_276;
}
}
else
{
lean_dec(x_264);
lean_dec(x_240);
x_265 = x_5;
x_266 = x_6;
x_267 = x_7;
x_268 = x_8;
x_269 = x_9;
goto block_276;
}
block_276:
{
lean_object* x_270; 
lean_inc(x_269);
lean_inc_ref(x_268);
lean_inc(x_267);
lean_inc_ref(x_266);
lean_inc(x_223);
x_270 = l_Lean_Meta_isExprDefEq(x_222, x_223, x_266, x_267, x_268, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
uint8_t x_273; 
lean_dec_ref(x_270);
x_273 = l_Lean_Expr_isFVar(x_223);
if (x_273 == 0)
{
x_224 = x_266;
x_225 = x_269;
x_226 = lean_box(0);
x_227 = x_268;
x_228 = x_267;
x_229 = x_265;
x_230 = x_273;
goto block_238;
}
else
{
lean_object* x_274; uint8_t x_275; 
x_274 = l_Lean_Expr_fvarId_x21(x_223);
x_275 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_274, x_4);
lean_dec(x_274);
x_224 = x_266;
x_225 = x_269;
x_226 = lean_box(0);
x_227 = x_268;
x_228 = x_267;
x_229 = x_265;
x_230 = x_275;
goto block_238;
}
}
else
{
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_223);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_270;
}
}
else
{
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_223);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_270;
}
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_240);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_286 = !lean_is_exclusive(x_241);
if (x_286 == 0)
{
return x_241;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_241, 0);
lean_inc(x_287);
lean_dec(x_241);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_289 = !lean_is_exclusive(x_239);
if (x_289 == 0)
{
return x_239;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_239, 0);
lean_inc(x_290);
lean_dec(x_239);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
block_238:
{
if (x_230 == 0)
{
lean_dec(x_223);
x_118 = x_229;
x_119 = x_224;
x_120 = x_228;
x_121 = x_227;
x_122 = x_225;
x_123 = lean_box(0);
goto block_217;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_3);
x_231 = l_Lean_Expr_fvarId_x21(x_223);
lean_dec(x_223);
lean_inc(x_225);
lean_inc_ref(x_227);
lean_inc(x_228);
lean_inc_ref(x_224);
lean_inc(x_229);
x_232 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(x_11, x_231, x_229, x_224, x_228, x_227, x_225);
lean_dec(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_apply_7(x_2, x_233, x_229, x_224, x_228, x_227, x_225, lean_box(0));
return x_234;
}
else
{
uint8_t x_235; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_2);
x_235 = !lean_is_exclusive(x_232);
if (x_235 == 0)
{
return x_232;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
lean_dec(x_232);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
}
}
else
{
lean_dec(x_219);
x_118 = x_5;
x_119 = x_6;
x_120 = x_7;
x_121 = x_8;
x_122 = x_9;
x_123 = lean_box(0);
goto block_217;
}
}
else
{
uint8_t x_292; 
lean_dec(x_117);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_292 = !lean_is_exclusive(x_218);
if (x_292 == 0)
{
return x_218;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_218, 0);
lean_inc(x_293);
lean_dec(x_218);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
block_217:
{
lean_object* x_124; 
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
x_124 = l_Lean_Meta_matchHEq_x3f(x_117, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_125) == 1)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
x_133 = l_Lean_Meta_isExprDefEq(x_129, x_131, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unbox(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
x_136 = l_Lean_Meta_isConstructorApp_x3f(x_130, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
x_138 = l_Lean_Meta_isConstructorApp_x3f(x_132, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_138) == 0)
{
if (lean_obj_tag(x_137) == 1)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
if (lean_obj_tag(x_140) == 1)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
lean_dec_ref(x_137);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
lean_dec(x_141);
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_dec_ref(x_140);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec_ref(x_142);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_name_eq(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_138, 0, x_134);
return x_138;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_138);
x_148 = lean_box(1);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_3);
x_149 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_148, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_free_object(x_149);
lean_dec(x_134);
x_40 = x_118;
x_41 = x_119;
x_42 = x_120;
x_43 = x_121;
x_44 = x_122;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_149, 0, x_134);
return x_149;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_dec(x_134);
x_40 = x_118;
x_41 = x_119;
x_42 = x_120;
x_43 = x_121;
x_44 = x_122;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_155; 
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_134);
return x_155;
}
}
}
else
{
lean_dec(x_134);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_149;
}
}
}
else
{
uint8_t x_156; 
lean_free_object(x_138);
lean_dec(x_140);
lean_dec_ref(x_137);
x_156 = lean_unbox(x_134);
lean_dec(x_134);
x_93 = x_156;
x_94 = x_118;
x_95 = x_119;
x_96 = x_120;
x_97 = x_121;
x_98 = x_122;
x_99 = lean_box(0);
goto block_110;
}
}
else
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_138, 0);
lean_inc(x_157);
lean_dec(x_138);
if (lean_obj_tag(x_157) == 1)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_158 = lean_ctor_get(x_137, 0);
lean_inc(x_158);
lean_dec_ref(x_137);
x_159 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_159);
lean_dec(x_158);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec_ref(x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
lean_dec(x_160);
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
lean_dec_ref(x_159);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = lean_name_eq(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_134);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_box(1);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_3);
x_167 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_166, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_unbox(x_168);
lean_dec(x_168);
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_134);
x_40 = x_118;
x_41 = x_119;
x_42 = x_120;
x_43 = x_121;
x_44 = x_122;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_171; 
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 1, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_134);
return x_171;
}
}
else
{
lean_dec(x_134);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_167;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_157);
lean_dec_ref(x_137);
x_172 = lean_unbox(x_134);
lean_dec(x_134);
x_93 = x_172;
x_94 = x_118;
x_95 = x_119;
x_96 = x_120;
x_97 = x_121;
x_98 = x_122;
x_99 = lean_box(0);
goto block_110;
}
}
}
else
{
uint8_t x_173; 
lean_dec_ref(x_138);
lean_dec(x_137);
x_173 = lean_unbox(x_134);
lean_dec(x_134);
x_93 = x_173;
x_94 = x_118;
x_95 = x_119;
x_96 = x_120;
x_97 = x_121;
x_98 = x_122;
x_99 = lean_box(0);
goto block_110;
}
}
else
{
uint8_t x_174; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_174 = !lean_is_exclusive(x_138);
if (x_174 == 0)
{
return x_138;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_138, 0);
lean_inc(x_175);
lean_dec(x_138);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_177 = !lean_is_exclusive(x_136);
if (x_177 == 0)
{
return x_136;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_136, 0);
lean_inc(x_178);
lean_dec(x_136);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; lean_object* x_181; 
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_13);
x_180 = lean_unbox(x_134);
lean_dec(x_134);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
x_181 = l_Lean_Meta_heqToEq(x_3, x_11, x_180, x_119, x_120, x_121, x_122);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 1);
x_185 = lean_st_ref_take(x_118);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_185, 2);
x_188 = lean_ctor_get(x_185, 0);
lean_dec(x_188);
lean_ctor_set_tag(x_182, 1);
lean_ctor_set(x_182, 1, x_187);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 0, x_184);
x_189 = lean_st_ref_set(x_118, x_185);
x_190 = lean_box(0);
x_191 = lean_apply_7(x_2, x_190, x_118, x_119, x_120, x_121, x_122, lean_box(0));
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_ctor_get(x_185, 1);
x_193 = lean_ctor_get(x_185, 2);
x_194 = lean_ctor_get(x_185, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_185);
lean_ctor_set_tag(x_182, 1);
lean_ctor_set(x_182, 1, x_193);
x_195 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_182);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_st_ref_set(x_118, x_195);
x_197 = lean_box(0);
x_198 = lean_apply_7(x_2, x_197, x_118, x_119, x_120, x_121, x_122, lean_box(0));
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_199 = lean_ctor_get(x_182, 0);
x_200 = lean_ctor_get(x_182, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_182);
x_201 = lean_st_ref_take(x_118);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 3);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 4, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_202);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_204);
x_208 = lean_st_ref_set(x_118, x_207);
x_209 = lean_box(0);
x_210 = lean_apply_7(x_2, x_209, x_118, x_119, x_120, x_121, x_122, lean_box(0));
return x_210;
}
}
else
{
uint8_t x_211; 
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_2);
x_211 = !lean_is_exclusive(x_181);
if (x_211 == 0)
{
return x_181;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_181, 0);
lean_inc(x_212);
lean_dec(x_181);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
}
else
{
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_133;
}
}
else
{
lean_dec(x_125);
x_40 = x_118;
x_41 = x_119;
x_42 = x_120;
x_43 = x_121;
x_44 = x_122;
x_45 = lean_box(0);
goto block_92;
}
}
else
{
uint8_t x_214; 
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_214 = !lean_is_exclusive(x_124);
if (x_214 == 0)
{
return x_124;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_124, 0);
lean_inc(x_215);
lean_dec(x_124);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_295 = !lean_is_exclusive(x_116);
if (x_295 == 0)
{
return x_116;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_116, 0);
lean_inc(x_296);
lean_dec(x_116);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_298 = lean_ctor_get(x_111, 0);
x_299 = lean_ctor_get(x_111, 1);
x_300 = lean_ctor_get(x_111, 3);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_111);
x_301 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
lean_ctor_set(x_301, 2, x_12);
lean_ctor_set(x_301, 3, x_300);
x_302 = lean_st_ref_set(x_5, x_301);
lean_inc(x_11);
x_303 = l_Lean_mkFVar(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_304 = lean_infer_type(x_303, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_374; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_305);
x_374 = l_Lean_Meta_matchEq_x3f(x_305, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec_ref(x_374);
if (lean_obj_tag(x_375) == 1)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_395; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_378);
x_395 = l_Lean_Meta_isConstructorApp_x3f(x_378, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec_ref(x_395);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_379);
x_397 = l_Lean_Meta_isConstructorApp_x3f(x_379, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
if (lean_obj_tag(x_396) == 1)
{
if (lean_obj_tag(x_398) == 1)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_412 = lean_ctor_get(x_396, 0);
lean_inc(x_412);
lean_dec_ref(x_396);
x_413 = lean_ctor_get(x_412, 0);
lean_inc_ref(x_413);
lean_dec(x_412);
x_414 = lean_ctor_get(x_398, 0);
lean_inc(x_414);
lean_dec_ref(x_398);
x_415 = lean_ctor_get(x_414, 0);
lean_inc_ref(x_415);
lean_dec(x_414);
x_416 = lean_ctor_get(x_413, 0);
lean_inc(x_416);
lean_dec_ref(x_413);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
lean_dec_ref(x_415);
x_418 = lean_name_eq(x_416, x_417);
lean_dec(x_417);
lean_dec(x_416);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_419 = lean_box(x_418);
if (lean_is_scalar(x_399)) {
 x_420 = lean_alloc_ctor(0, 1, 0);
} else {
 x_420 = x_399;
}
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
else
{
lean_dec(x_399);
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = x_9;
goto block_411;
}
}
else
{
lean_dec(x_399);
lean_dec(x_398);
lean_dec_ref(x_396);
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = x_9;
goto block_411;
}
}
else
{
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_396);
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = x_9;
goto block_411;
}
block_411:
{
lean_object* x_405; 
lean_inc(x_404);
lean_inc_ref(x_403);
lean_inc(x_402);
lean_inc_ref(x_401);
lean_inc(x_379);
x_405 = l_Lean_Meta_isExprDefEq(x_378, x_379, x_401, x_402, x_403, x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_unbox(x_406);
lean_dec(x_406);
if (x_407 == 0)
{
uint8_t x_408; 
lean_dec_ref(x_405);
x_408 = l_Lean_Expr_isFVar(x_379);
if (x_408 == 0)
{
x_380 = x_401;
x_381 = x_404;
x_382 = lean_box(0);
x_383 = x_403;
x_384 = x_402;
x_385 = x_400;
x_386 = x_408;
goto block_394;
}
else
{
lean_object* x_409; uint8_t x_410; 
x_409 = l_Lean_Expr_fvarId_x21(x_379);
x_410 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_409, x_4);
lean_dec(x_409);
x_380 = x_401;
x_381 = x_404;
x_382 = lean_box(0);
x_383 = x_403;
x_384 = x_402;
x_385 = x_400;
x_386 = x_410;
goto block_394;
}
}
else
{
lean_dec(x_404);
lean_dec_ref(x_403);
lean_dec(x_402);
lean_dec_ref(x_401);
lean_dec(x_400);
lean_dec(x_379);
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_405;
}
}
else
{
lean_dec(x_404);
lean_dec_ref(x_403);
lean_dec(x_402);
lean_dec_ref(x_401);
lean_dec(x_400);
lean_dec(x_379);
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_405;
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_396);
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_421 = lean_ctor_get(x_397, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_422 = x_397;
} else {
 lean_dec_ref(x_397);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_424 = lean_ctor_get(x_395, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_425 = x_395;
} else {
 lean_dec_ref(x_395);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
block_394:
{
if (x_386 == 0)
{
lean_dec(x_379);
x_306 = x_385;
x_307 = x_380;
x_308 = x_384;
x_309 = x_383;
x_310 = x_381;
x_311 = lean_box(0);
goto block_373;
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_3);
x_387 = l_Lean_Expr_fvarId_x21(x_379);
lean_dec(x_379);
lean_inc(x_381);
lean_inc_ref(x_383);
lean_inc(x_384);
lean_inc_ref(x_380);
lean_inc(x_385);
x_388 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(x_11, x_387, x_385, x_380, x_384, x_383, x_381);
lean_dec(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
x_390 = lean_apply_7(x_2, x_389, x_385, x_380, x_384, x_383, x_381, lean_box(0));
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec_ref(x_383);
lean_dec(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_2);
x_391 = lean_ctor_get(x_388, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_392 = x_388;
} else {
 lean_dec_ref(x_388);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
}
}
else
{
lean_dec(x_375);
x_306 = x_5;
x_307 = x_6;
x_308 = x_7;
x_309 = x_8;
x_310 = x_9;
x_311 = lean_box(0);
goto block_373;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_305);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_427 = lean_ctor_get(x_374, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_428 = x_374;
} else {
 lean_dec_ref(x_374);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
block_373:
{
lean_object* x_312; 
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
x_312 = l_Lean_Meta_matchHEq_x3f(x_305, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec_ref(x_312);
if (lean_obj_tag(x_313) == 1)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 0);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_ctor_get(x_315, 0);
lean_inc(x_318);
lean_dec(x_315);
x_319 = lean_ctor_get(x_316, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_316, 1);
lean_inc(x_320);
lean_dec(x_316);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
x_321 = l_Lean_Meta_isExprDefEq(x_317, x_319, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; uint8_t x_323; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
x_323 = lean_unbox(x_322);
if (x_323 == 0)
{
lean_object* x_324; 
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
x_324 = l_Lean_Meta_isConstructorApp_x3f(x_318, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
lean_dec_ref(x_324);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
x_326 = l_Lean_Meta_isConstructorApp_x3f(x_320, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_325) == 1)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
if (lean_obj_tag(x_327) == 1)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_329 = lean_ctor_get(x_325, 0);
lean_inc(x_329);
lean_dec_ref(x_325);
x_330 = lean_ctor_get(x_329, 0);
lean_inc_ref(x_330);
lean_dec(x_329);
x_331 = lean_ctor_get(x_327, 0);
lean_inc(x_331);
lean_dec_ref(x_327);
x_332 = lean_ctor_get(x_331, 0);
lean_inc_ref(x_332);
lean_dec(x_331);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_dec_ref(x_330);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
lean_dec_ref(x_332);
x_335 = lean_name_eq(x_333, x_334);
lean_dec(x_334);
lean_dec(x_333);
if (x_335 == 0)
{
lean_object* x_336; 
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_328)) {
 x_336 = lean_alloc_ctor(0, 1, 0);
} else {
 x_336 = x_328;
}
lean_ctor_set(x_336, 0, x_322);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_328);
x_337 = lean_box(1);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
lean_inc(x_3);
x_338 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_337, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_340 = x_338;
} else {
 lean_dec_ref(x_338);
 x_340 = lean_box(0);
}
x_341 = lean_unbox(x_339);
lean_dec(x_339);
if (x_341 == 0)
{
lean_dec(x_340);
lean_dec(x_322);
x_40 = x_306;
x_41 = x_307;
x_42 = x_308;
x_43 = x_309;
x_44 = x_310;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_342; 
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(0, 1, 0);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_322);
return x_342;
}
}
else
{
lean_dec(x_322);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_338;
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec_ref(x_325);
x_343 = lean_unbox(x_322);
lean_dec(x_322);
x_93 = x_343;
x_94 = x_306;
x_95 = x_307;
x_96 = x_308;
x_97 = x_309;
x_98 = x_310;
x_99 = lean_box(0);
goto block_110;
}
}
else
{
uint8_t x_344; 
lean_dec_ref(x_326);
lean_dec(x_325);
x_344 = lean_unbox(x_322);
lean_dec(x_322);
x_93 = x_344;
x_94 = x_306;
x_95 = x_307;
x_96 = x_308;
x_97 = x_309;
x_98 = x_310;
x_99 = lean_box(0);
goto block_110;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_325);
lean_dec(x_322);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_345 = lean_ctor_get(x_326, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_346 = x_326;
} else {
 lean_dec_ref(x_326);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_348 = lean_ctor_get(x_324, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_349 = x_324;
} else {
 lean_dec_ref(x_324);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
else
{
uint8_t x_351; lean_object* x_352; 
lean_dec(x_320);
lean_dec(x_318);
lean_dec(x_13);
x_351 = lean_unbox(x_322);
lean_dec(x_322);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc_ref(x_307);
x_352 = l_Lean_Meta_heqToEq(x_3, x_11, x_351, x_307, x_308, x_309, x_310);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = lean_st_ref_take(x_306);
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 2);
lean_inc(x_359);
x_360 = lean_ctor_get(x_357, 3);
lean_inc(x_360);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_361 = x_357;
} else {
 lean_dec_ref(x_357);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_356;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_354);
lean_ctor_set(x_362, 1, x_359);
if (lean_is_scalar(x_361)) {
 x_363 = lean_alloc_ctor(0, 4, 0);
} else {
 x_363 = x_361;
}
lean_ctor_set(x_363, 0, x_355);
lean_ctor_set(x_363, 1, x_358);
lean_ctor_set(x_363, 2, x_362);
lean_ctor_set(x_363, 3, x_360);
x_364 = lean_st_ref_set(x_306, x_363);
x_365 = lean_box(0);
x_366 = lean_apply_7(x_2, x_365, x_306, x_307, x_308, x_309, x_310, lean_box(0));
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec_ref(x_2);
x_367 = lean_ctor_get(x_352, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_368 = x_352;
} else {
 lean_dec_ref(x_352);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
}
else
{
lean_dec(x_320);
lean_dec(x_318);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_321;
}
}
else
{
lean_dec(x_313);
x_40 = x_306;
x_41 = x_307;
x_42 = x_308;
x_43 = x_309;
x_44 = x_310;
x_45 = lean_box(0);
goto block_92;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_370 = lean_ctor_get(x_312, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 x_371 = x_312;
} else {
 lean_dec_ref(x_312);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_370);
return x_372;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_430 = lean_ctor_get(x_304, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_431 = x_304;
} else {
 lean_dec_ref(x_304);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
block_39:
{
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec_ref(x_20);
x_22 = lean_st_ref_take(x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 3);
if (lean_is_scalar(x_13)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_13;
}
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 3, x_25);
x_26 = lean_st_ref_set(x_19, x_22);
x_27 = lean_box(0);
x_28 = lean_apply_7(x_2, x_27, x_19, x_14, x_18, x_17, x_15, lean_box(0));
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
x_31 = lean_ctor_get(x_22, 2);
x_32 = lean_ctor_get(x_22, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
if (lean_is_scalar(x_13)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_13;
}
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_st_ref_set(x_19, x_34);
x_36 = lean_box(0);
x_37 = lean_apply_7(x_2, x_36, x_19, x_14, x_18, x_17, x_15, lean_box(0));
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_2);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_20);
return x_38;
}
}
block_92:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_11);
x_47 = l_Lean_Meta_injection(x_3, x_11, x_46, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_2);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_free_object(x_47);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_53);
lean_dec_ref(x_49);
x_54 = lean_st_ref_take(x_40);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_54, 2);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_array_to_list(x_53);
x_59 = l_List_appendTR___redArg(x_58, x_56);
lean_ctor_set(x_54, 2, x_59);
lean_ctor_set(x_54, 0, x_52);
x_60 = lean_st_ref_set(x_40, x_54);
x_61 = lean_box(0);
x_62 = lean_apply_7(x_2, x_61, x_40, x_41, x_42, x_43, x_44, lean_box(0));
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_54, 1);
x_64 = lean_ctor_get(x_54, 2);
x_65 = lean_ctor_get(x_54, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_66 = lean_array_to_list(x_53);
x_67 = l_List_appendTR___redArg(x_66, x_64);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_65);
x_69 = lean_st_ref_set(x_40, x_68);
x_70 = lean_box(0);
x_71 = lean_apply_7(x_2, x_70, x_40, x_41, x_42, x_43, x_44, lean_box(0));
return x_71;
}
}
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_47, 0);
lean_inc(x_72);
lean_dec(x_47);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_2);
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_77);
lean_dec_ref(x_72);
x_78 = lean_st_ref_take(x_40);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_array_to_list(x_77);
x_84 = l_List_appendTR___redArg(x_83, x_80);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 4, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_81);
x_86 = lean_st_ref_set(x_40, x_85);
x_87 = lean_box(0);
x_88 = lean_apply_7(x_2, x_87, x_40, x_41, x_42, x_43, x_44, lean_box(0));
return x_88;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_47, 0);
lean_inc(x_89);
lean_dec_ref(x_47);
x_90 = l_Lean_Exception_isInterrupt(x_89);
if (x_90 == 0)
{
uint8_t x_91; 
lean_inc(x_89);
x_91 = l_Lean_Exception_isRuntime(x_89);
x_14 = x_41;
x_15 = x_44;
x_16 = lean_box(0);
x_17 = x_43;
x_18 = x_42;
x_19 = x_40;
x_20 = x_89;
x_21 = x_91;
goto block_39;
}
else
{
x_14 = x_41;
x_15 = x_44;
x_16 = lean_box(0);
x_17 = x_43;
x_18 = x_42;
x_19 = x_40;
x_20 = x_89;
x_21 = x_90;
goto block_39;
}
}
}
block_110:
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_box(1);
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc(x_96);
lean_inc_ref(x_95);
lean_inc(x_3);
x_101 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_100, x_95, x_96, x_97, x_98);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_free_object(x_101);
x_40 = x_94;
x_41 = x_95;
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_105; 
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = lean_box(x_93);
lean_ctor_set(x_101, 0, x_105);
return x_101;
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
x_40 = x_94;
x_41 = x_95;
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_108 = lean_box(x_93);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_101;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_3);
lean_dec(x_1);
x_433 = lean_box(0);
x_434 = lean_apply_7(x_2, x_433, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_434;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed), 7, 0);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_9);
x_13 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(x_8, x_12, x_1, x_2, x_3, x_4, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_dec_ref(x_10);
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_instBEqFVarId_beq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_5 = lean_st_ref_get(x_3);
x_29 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_29);
lean_dec(x_5);
x_30 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__0___boxed), 1, 0);
x_31 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_2);
x_32 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1;
lean_inc_ref(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = l_Lean_Expr_hasFVar(x_1);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_1);
if (x_35 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_1);
x_6 = x_35;
x_7 = x_29;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec_ref(x_29);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_31, x_30, x_1, x_33);
x_23 = x_36;
goto block_28;
}
}
else
{
lean_object* x_37; 
lean_dec_ref(x_29);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_31, x_30, x_1, x_33);
x_23 = x_37;
goto block_28;
}
block_22:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_7);
x_11 = lean_st_ref_set(x_3, x_8);
x_12 = lean_box(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_ctor_get(x_8, 2);
x_16 = lean_ctor_get(x_8, 3);
x_17 = lean_ctor_get(x_8, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_3, x_18);
x_20 = lean_box(x_6);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
lean_dec(x_24);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
x_6 = x_27;
x_7 = x_26;
goto block_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg(x_1, x_4);
return x_7;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec_ref(x_4);
lean_inc(x_12);
lean_inc_ref(x_5);
x_14 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg(x_5, x_12, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_12);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_mkFVar(x_12);
x_19 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Meta_mkForallFVars(x_20, x_5, x_1, x_2, x_2, x_3, x_6, x_7, x_8, x_9);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_4 = x_13;
x_5 = x_22;
goto _start;
}
else
{
lean_dec(x_13);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_sub(x_9, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_mkFVar(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
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
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Match", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchEqs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2;
x_2 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1;
x_3 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simplified hypothesis", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_3, x_4, x_4, x_5, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_List_reverse___redArg(x_6);
x_15 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg(x_3, x_4, x_5, x_14, x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_32 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3;
x_33 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg(x_32, x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5;
lean_inc(x_16);
x_37 = l_Lean_indentExpr(x_16);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5(x_32, x_38, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
block_31:
{
lean_object* x_22; 
lean_inc(x_16);
x_22 = l_Lean_Meta_check(x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_16);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
static uint64_t _init_l_Lean_Meta_Match_simpH_x3f___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_simpH_x3f___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_simpH_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_simpH_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_simpH_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Meta_Match_simpH_x3f___lam__1(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Context_config(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint64_t x_22; uint8_t x_23; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__0___boxed), 8, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = 0;
x_21 = 1;
lean_ctor_set_uint8(x_8, 9, x_21);
x_22 = l_Lean_Meta_Context_configKey(x_3);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_3, 6);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 0);
lean_dec(x_30);
x_31 = 2;
x_32 = lean_uint64_shift_right(x_22, x_31);
x_33 = lean_uint64_shift_left(x_32, x_31);
x_34 = l_Lean_Meta_Match_simpH_x3f___closed__0;
x_35 = lean_uint64_lor(x_33, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_35);
lean_ctor_set(x_3, 0, x_36);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(x_1, x_19, x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_box(0);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_39, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Expr_mvarId_x21(x_41);
lean_dec(x_41);
x_43 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_44 = l_Lean_Meta_introNCore(x_42, x_38, x_43, x_20, x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_48 = l_Lean_Meta_introNCore(x_47, x_2, x_43, x_20, x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_array_to_list(x_46);
x_53 = lean_array_to_list(x_50);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_43);
x_55 = lean_st_mk_ref(x_54);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_55);
x_56 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_55, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_st_ref_get(x_55);
lean_dec(x_55);
x_60 = lean_unbox(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_61 = lean_box(0);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_56);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
lean_dec(x_59);
x_65 = l_List_reverse___redArg(x_64);
x_66 = lean_array_mk(x_65);
x_67 = lean_array_size(x_66);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(x_67, x_68, x_66);
x_70 = l_Lean_Meta_Match_simpH_x3f___closed__3;
x_71 = 1;
x_72 = lean_box(x_20);
x_73 = lean_box(x_71);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__1___boxed), 11, 6);
lean_closure_set(x_74, 0, x_69);
lean_closure_set(x_74, 1, x_70);
lean_closure_set(x_74, 2, x_72);
lean_closure_set(x_74, 3, x_58);
lean_closure_set(x_74, 4, x_73);
lean_closure_set(x_74, 5, x_63);
x_75 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_62, x_74, x_3, x_4, x_5, x_6);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_56, 0);
lean_inc(x_76);
lean_dec(x_56);
x_77 = lean_st_ref_get(x_55);
lean_dec(x_55);
x_78 = lean_unbox(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 3);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l_List_reverse___redArg(x_83);
x_85 = lean_array_mk(x_84);
x_86 = lean_array_size(x_85);
x_87 = 0;
x_88 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(x_86, x_87, x_85);
x_89 = l_Lean_Meta_Match_simpH_x3f___closed__3;
x_90 = 1;
x_91 = lean_box(x_20);
x_92 = lean_box(x_90);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__1___boxed), 11, 6);
lean_closure_set(x_93, 0, x_88);
lean_closure_set(x_93, 1, x_89);
lean_closure_set(x_93, 2, x_91);
lean_closure_set(x_93, 3, x_76);
lean_closure_set(x_93, 4, x_92);
lean_closure_set(x_93, 5, x_82);
x_94 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_81, x_93, x_3, x_4, x_5, x_6);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_55);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_56);
if (x_95 == 0)
{
return x_56;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_56, 0);
lean_inc(x_96);
lean_dec(x_56);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_46);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_48);
if (x_98 == 0)
{
return x_48;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_48, 0);
lean_inc(x_99);
lean_dec(x_48);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_44);
if (x_101 == 0)
{
return x_44;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_44, 0);
lean_inc(x_102);
lean_dec(x_44);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_38);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_40);
if (x_104 == 0)
{
return x_40;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_40, 0);
lean_inc(x_105);
lean_dec(x_40);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_37);
if (x_107 == 0)
{
return x_37;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
lean_dec(x_37);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_3);
x_110 = 2;
x_111 = lean_uint64_shift_right(x_22, x_110);
x_112 = lean_uint64_shift_left(x_111, x_110);
x_113 = l_Lean_Meta_Match_simpH_x3f___closed__0;
x_114 = lean_uint64_lor(x_112, x_113);
x_115 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_115, 0, x_8);
lean_ctor_set_uint64(x_115, sizeof(void*)*1, x_114);
x_116 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_11);
lean_ctor_set(x_116, 2, x_12);
lean_ctor_set(x_116, 3, x_13);
lean_ctor_set(x_116, 4, x_14);
lean_ctor_set(x_116, 5, x_15);
lean_ctor_set(x_116, 6, x_16);
lean_ctor_set_uint8(x_116, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_116, sizeof(void*)*7 + 1, x_17);
lean_ctor_set_uint8(x_116, sizeof(void*)*7 + 2, x_18);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_116);
lean_inc_ref(x_1);
x_117 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(x_1, x_19, x_20, x_116, x_4, x_5, x_6);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_box(0);
lean_inc_ref(x_116);
x_120 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_119, x_116, x_4, x_5, x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = l_Lean_Expr_mvarId_x21(x_121);
lean_dec(x_121);
x_123 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_116);
x_124 = l_Lean_Meta_introNCore(x_122, x_118, x_123, x_20, x_20, x_116, x_4, x_5, x_6);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_116);
x_128 = l_Lean_Meta_introNCore(x_127, x_2, x_123, x_20, x_20, x_116, x_4, x_5, x_6);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_array_to_list(x_126);
x_133 = lean_array_to_list(x_130);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_123);
x_135 = lean_st_mk_ref(x_134);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_116);
lean_inc(x_135);
x_136 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_135, x_116, x_4, x_5, x_6);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_st_ref_get(x_135);
lean_dec(x_135);
x_140 = lean_unbox(x_137);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_141 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_138;
}
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_138);
x_143 = lean_ctor_get(x_139, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 3);
lean_inc(x_145);
lean_dec(x_139);
x_146 = l_List_reverse___redArg(x_145);
x_147 = lean_array_mk(x_146);
x_148 = lean_array_size(x_147);
x_149 = 0;
x_150 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(x_148, x_149, x_147);
x_151 = l_Lean_Meta_Match_simpH_x3f___closed__3;
x_152 = 1;
x_153 = lean_box(x_20);
x_154 = lean_box(x_152);
x_155 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__1___boxed), 11, 6);
lean_closure_set(x_155, 0, x_150);
lean_closure_set(x_155, 1, x_151);
lean_closure_set(x_155, 2, x_153);
lean_closure_set(x_155, 3, x_137);
lean_closure_set(x_155, 4, x_154);
lean_closure_set(x_155, 5, x_144);
x_156 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_143, x_155, x_116, x_4, x_5, x_6);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_135);
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_157 = lean_ctor_get(x_136, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_158 = x_136;
} else {
 lean_dec_ref(x_136);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_126);
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_160 = lean_ctor_get(x_128, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_161 = x_128;
} else {
 lean_dec_ref(x_128);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_163 = lean_ctor_get(x_124, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_164 = x_124;
} else {
 lean_dec_ref(x_124);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_118);
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_166 = lean_ctor_get(x_120, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_167 = x_120;
} else {
 lean_dec_ref(x_120);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_116);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = lean_ctor_get(x_117, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_170 = x_117;
} else {
 lean_dec_ref(x_117);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
}
else
{
uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; lean_object* x_202; uint64_t x_203; lean_object* x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_172 = lean_ctor_get_uint8(x_8, 0);
x_173 = lean_ctor_get_uint8(x_8, 1);
x_174 = lean_ctor_get_uint8(x_8, 2);
x_175 = lean_ctor_get_uint8(x_8, 3);
x_176 = lean_ctor_get_uint8(x_8, 4);
x_177 = lean_ctor_get_uint8(x_8, 5);
x_178 = lean_ctor_get_uint8(x_8, 6);
x_179 = lean_ctor_get_uint8(x_8, 7);
x_180 = lean_ctor_get_uint8(x_8, 8);
x_181 = lean_ctor_get_uint8(x_8, 10);
x_182 = lean_ctor_get_uint8(x_8, 11);
x_183 = lean_ctor_get_uint8(x_8, 12);
x_184 = lean_ctor_get_uint8(x_8, 13);
x_185 = lean_ctor_get_uint8(x_8, 14);
x_186 = lean_ctor_get_uint8(x_8, 15);
x_187 = lean_ctor_get_uint8(x_8, 16);
x_188 = lean_ctor_get_uint8(x_8, 17);
x_189 = lean_ctor_get_uint8(x_8, 18);
lean_dec(x_8);
x_190 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_191 = lean_ctor_get(x_3, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_3, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_3, 5);
lean_inc(x_195);
x_196 = lean_ctor_get(x_3, 6);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_198 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
lean_inc(x_2);
x_199 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__0___boxed), 8, 1);
lean_closure_set(x_199, 0, x_2);
x_200 = 0;
x_201 = 1;
x_202 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_202, 0, x_172);
lean_ctor_set_uint8(x_202, 1, x_173);
lean_ctor_set_uint8(x_202, 2, x_174);
lean_ctor_set_uint8(x_202, 3, x_175);
lean_ctor_set_uint8(x_202, 4, x_176);
lean_ctor_set_uint8(x_202, 5, x_177);
lean_ctor_set_uint8(x_202, 6, x_178);
lean_ctor_set_uint8(x_202, 7, x_179);
lean_ctor_set_uint8(x_202, 8, x_180);
lean_ctor_set_uint8(x_202, 9, x_201);
lean_ctor_set_uint8(x_202, 10, x_181);
lean_ctor_set_uint8(x_202, 11, x_182);
lean_ctor_set_uint8(x_202, 12, x_183);
lean_ctor_set_uint8(x_202, 13, x_184);
lean_ctor_set_uint8(x_202, 14, x_185);
lean_ctor_set_uint8(x_202, 15, x_186);
lean_ctor_set_uint8(x_202, 16, x_187);
lean_ctor_set_uint8(x_202, 17, x_188);
lean_ctor_set_uint8(x_202, 18, x_189);
x_203 = l_Lean_Meta_Context_configKey(x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_204 = x_3;
} else {
 lean_dec_ref(x_3);
 x_204 = lean_box(0);
}
x_205 = 2;
x_206 = lean_uint64_shift_right(x_203, x_205);
x_207 = lean_uint64_shift_left(x_206, x_205);
x_208 = l_Lean_Meta_Match_simpH_x3f___closed__0;
x_209 = lean_uint64_lor(x_207, x_208);
x_210 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set_uint64(x_210, sizeof(void*)*1, x_209);
if (lean_is_scalar(x_204)) {
 x_211 = lean_alloc_ctor(0, 7, 3);
} else {
 x_211 = x_204;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_191);
lean_ctor_set(x_211, 2, x_192);
lean_ctor_set(x_211, 3, x_193);
lean_ctor_set(x_211, 4, x_194);
lean_ctor_set(x_211, 5, x_195);
lean_ctor_set(x_211, 6, x_196);
lean_ctor_set_uint8(x_211, sizeof(void*)*7, x_190);
lean_ctor_set_uint8(x_211, sizeof(void*)*7 + 1, x_197);
lean_ctor_set_uint8(x_211, sizeof(void*)*7 + 2, x_198);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_211);
lean_inc_ref(x_1);
x_212 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(x_1, x_199, x_200, x_211, x_4, x_5, x_6);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = lean_box(0);
lean_inc_ref(x_211);
x_215 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_214, x_211, x_4, x_5, x_6);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l_Lean_Expr_mvarId_x21(x_216);
lean_dec(x_216);
x_218 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_211);
x_219 = l_Lean_Meta_introNCore(x_217, x_213, x_218, x_200, x_200, x_211, x_4, x_5, x_6);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_211);
x_223 = l_Lean_Meta_introNCore(x_222, x_2, x_218, x_200, x_200, x_211, x_4, x_5, x_6);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_array_to_list(x_221);
x_228 = lean_array_to_list(x_225);
x_229 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_218);
x_230 = lean_st_mk_ref(x_229);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_211);
lean_inc(x_230);
x_231 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_230, x_211, x_4, x_5, x_6);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_st_ref_get(x_230);
lean_dec(x_230);
x_235 = lean_unbox(x_232);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_236 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_237 = lean_alloc_ctor(0, 1, 0);
} else {
 x_237 = x_233;
}
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; size_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_233);
x_238 = lean_ctor_get(x_234, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 3);
lean_inc(x_240);
lean_dec(x_234);
x_241 = l_List_reverse___redArg(x_240);
x_242 = lean_array_mk(x_241);
x_243 = lean_array_size(x_242);
x_244 = 0;
x_245 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(x_243, x_244, x_242);
x_246 = l_Lean_Meta_Match_simpH_x3f___closed__3;
x_247 = 1;
x_248 = lean_box(x_200);
x_249 = lean_box(x_247);
x_250 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH_x3f___lam__1___boxed), 11, 6);
lean_closure_set(x_250, 0, x_245);
lean_closure_set(x_250, 1, x_246);
lean_closure_set(x_250, 2, x_248);
lean_closure_set(x_250, 3, x_232);
lean_closure_set(x_250, 4, x_249);
lean_closure_set(x_250, 5, x_239);
x_251 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_238, x_250, x_211, x_4, x_5, x_6);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_230);
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_252 = lean_ctor_get(x_231, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_253 = x_231;
} else {
 lean_dec_ref(x_231);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_221);
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_255 = lean_ctor_get(x_223, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_256 = x_223;
} else {
 lean_dec_ref(x_223);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_258 = lean_ctor_get(x_219, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_259 = x_219;
} else {
 lean_dec_ref(x_219);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_261 = lean_ctor_get(x_215, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_262 = x_215;
} else {
 lean_dec_ref(x_215);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec_ref(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = lean_ctor_get(x_212, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_265 = x_212;
} else {
 lean_dec_ref(x_212);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
return x_266;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_3);
x_16 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3(x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Match_simpH_x3f_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_x3f_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_x3f_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_simpH_x3f_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_simpH_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_SimpH(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0);
l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0);
l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1 = _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1);
l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2 = _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2);
l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3 = _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3);
l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4 = _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3);
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0);
l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0 = _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__0);
l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1 = _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_x3f_spec__2___redArg___closed__1);
l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Meta_Match_simpH_x3f_spec__3___redArg___closed__0);
l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1 = _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Match_simpH_x3f_spec__5___closed__2);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__0);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__1);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__2);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__3);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__4);
l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5 = _init_l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___lam__1___closed__5);
l_Lean_Meta_Match_simpH_x3f___closed__0 = _init_l_Lean_Meta_Match_simpH_x3f___closed__0();
l_Lean_Meta_Match_simpH_x3f___closed__1 = _init_l_Lean_Meta_Match_simpH_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___closed__1);
l_Lean_Meta_Match_simpH_x3f___closed__2 = _init_l_Lean_Meta_Match_simpH_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___closed__2);
l_Lean_Meta_Match_simpH_x3f___closed__3 = _init_l_Lean_Meta_Match_simpH_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_simpH_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
