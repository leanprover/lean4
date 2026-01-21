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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0;
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2;
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Match_simpH___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0;
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(x_1);
lean_dec(x_1);
return x_3;
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
lean_dec_ref(x_9);
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
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_10);
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
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
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
x_9 = x_21;
x_10 = x_22;
x_11 = lean_box(0);
x_12 = x_25;
goto block_20;
}
else
{
x_9 = x_21;
x_10 = x_22;
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_93; uint8_t x_94; 
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
x_93 = lean_st_ref_take(x_5);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_93, 2);
lean_dec(x_95);
lean_ctor_set(x_93, 2, x_12);
x_96 = lean_st_ref_set(x_5, x_93);
lean_inc(x_11);
x_97 = l_Lean_mkFVar(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_98 = lean_infer_type(x_97, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_169; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_99);
x_169 = l_Lean_Meta_matchEq_x3f(x_99, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_174);
x_175 = l_Lean_Meta_isExprDefEq(x_173, x_174, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; uint8_t x_186; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_186 = lean_unbox(x_176);
lean_dec(x_176);
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = l_Lean_Expr_isFVar(x_174);
if (x_187 == 0)
{
x_177 = x_187;
goto block_185;
}
else
{
lean_object* x_188; uint8_t x_189; 
x_188 = l_Lean_Expr_fvarId_x21(x_174);
x_189 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_188, x_4);
lean_dec(x_188);
x_177 = x_189;
goto block_185;
}
}
else
{
lean_object* x_190; 
lean_dec(x_174);
lean_dec(x_99);
lean_dec(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_190 = l_Lean_MVarId_clear(x_3, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_st_ref_take(x_5);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
lean_ctor_set(x_192, 0, x_191);
x_195 = lean_st_ref_set(x_5, x_192);
x_196 = lean_box(0);
x_197 = lean_apply_7(x_2, x_196, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_192, 1);
x_199 = lean_ctor_get(x_192, 2);
x_200 = lean_ctor_get(x_192, 3);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_192);
x_201 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_199);
lean_ctor_set(x_201, 3, x_200);
x_202 = lean_st_ref_set(x_5, x_201);
x_203 = lean_box(0);
x_204 = lean_apply_7(x_2, x_203, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_204;
}
}
else
{
uint8_t x_205; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_205 = !lean_is_exclusive(x_190);
if (x_205 == 0)
{
return x_190;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_190, 0);
lean_inc(x_206);
lean_dec(x_190);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
block_185:
{
if (x_177 == 0)
{
lean_dec(x_174);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = lean_box(0);
goto block_168;
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_99);
lean_dec(x_13);
lean_dec(x_3);
x_178 = l_Lean_Expr_fvarId_x21(x_174);
lean_dec(x_174);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_179 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(x_11, x_178, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = lean_apply_7(x_2, x_180, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_181;
}
else
{
uint8_t x_182; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_182 = !lean_is_exclusive(x_179);
if (x_182 == 0)
{
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
}
}
else
{
lean_dec(x_174);
lean_dec(x_99);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_175;
}
}
else
{
lean_dec(x_170);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = lean_box(0);
goto block_168;
}
}
else
{
uint8_t x_208; 
lean_dec(x_99);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_208 = !lean_is_exclusive(x_169);
if (x_208 == 0)
{
return x_169;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_169, 0);
lean_inc(x_209);
lean_dec(x_169);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
block_168:
{
lean_object* x_106; 
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
x_106 = l_Lean_Meta_matchHEq_x3f(x_99, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
if (lean_obj_tag(x_107) == 1)
{
uint8_t x_108; lean_object* x_109; 
lean_dec_ref(x_107);
x_108 = 1;
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_11);
lean_inc(x_3);
x_109 = l_Lean_Meta_heqToEq(x_3, x_11, x_108, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = l_Lean_instBEqMVarId_beq(x_113, x_3);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_115 = lean_st_ref_take(x_100);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_115, 2);
x_118 = lean_ctor_get(x_115, 0);
lean_dec(x_118);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 1, x_117);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 0, x_113);
x_119 = lean_st_ref_set(x_100, x_115);
x_120 = lean_box(0);
x_121 = lean_apply_7(x_2, x_120, x_100, x_101, x_102, x_103, x_104, lean_box(0));
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_115, 1);
x_123 = lean_ctor_get(x_115, 2);
x_124 = lean_ctor_get(x_115, 3);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_115);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 1, x_123);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_110);
lean_ctor_set(x_125, 3, x_124);
x_126 = lean_st_ref_set(x_100, x_125);
x_127 = lean_box(0);
x_128 = lean_apply_7(x_2, x_127, x_100, x_101, x_102, x_103, x_104, lean_box(0));
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_free_object(x_110);
lean_dec(x_113);
lean_dec(x_112);
x_129 = lean_box(1);
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_3);
x_130 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_129, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_free_object(x_130);
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = lean_box(0);
goto block_92;
}
else
{
uint8_t x_134; lean_object* x_135; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_134 = 0;
x_135 = lean_box(x_134);
lean_ctor_set(x_130, 0, x_135);
return x_130;
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
lean_dec(x_130);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = lean_box(0);
goto block_92;
}
else
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = 0;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_130;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_110, 0);
x_142 = lean_ctor_get(x_110, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_110);
x_143 = l_Lean_instBEqMVarId_beq(x_142, x_3);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_144 = lean_st_ref_take(x_100);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_146);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 4, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_142);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_149);
lean_ctor_set(x_150, 3, x_147);
x_151 = lean_st_ref_set(x_100, x_150);
x_152 = lean_box(0);
x_153 = lean_apply_7(x_2, x_152, x_100, x_101, x_102, x_103, x_104, lean_box(0));
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_142);
lean_dec(x_141);
x_154 = lean_box(1);
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_3);
x_155 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_154, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_unbox(x_156);
lean_dec(x_156);
if (x_158 == 0)
{
lean_dec(x_157);
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = lean_box(0);
goto block_92;
}
else
{
uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_159 = 0;
x_160 = lean_box(x_159);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
else
{
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_155;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_162 = !lean_is_exclusive(x_109);
if (x_162 == 0)
{
return x_109;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_109, 0);
lean_inc(x_163);
lean_dec(x_109);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
else
{
lean_dec(x_107);
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = lean_box(0);
goto block_92;
}
}
else
{
uint8_t x_165; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_165 = !lean_is_exclusive(x_106);
if (x_165 == 0)
{
return x_106;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_106, 0);
lean_inc(x_166);
lean_dec(x_106);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_211 = !lean_is_exclusive(x_98);
if (x_211 == 0)
{
return x_98;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_98, 0);
lean_inc(x_212);
lean_dec(x_98);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_93, 0);
x_215 = lean_ctor_get(x_93, 1);
x_216 = lean_ctor_get(x_93, 3);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_93);
x_217 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
lean_ctor_set(x_217, 2, x_12);
lean_ctor_set(x_217, 3, x_216);
x_218 = lean_st_ref_set(x_5, x_217);
lean_inc(x_11);
x_219 = l_Lean_mkFVar(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_220 = lean_infer_type(x_219, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_262; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_221);
x_262 = l_Lean_Meta_matchEq_x3f(x_221, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
if (lean_obj_tag(x_263) == 1)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_267);
x_268 = l_Lean_Meta_isExprDefEq(x_266, x_267, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; uint8_t x_270; uint8_t x_279; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
lean_dec_ref(x_268);
x_279 = lean_unbox(x_269);
lean_dec(x_269);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = l_Lean_Expr_isFVar(x_267);
if (x_280 == 0)
{
x_270 = x_280;
goto block_278;
}
else
{
lean_object* x_281; uint8_t x_282; 
x_281 = l_Lean_Expr_fvarId_x21(x_267);
x_282 = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(x_281, x_4);
lean_dec(x_281);
x_270 = x_282;
goto block_278;
}
}
else
{
lean_object* x_283; 
lean_dec(x_267);
lean_dec(x_221);
lean_dec(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_283 = l_Lean_MVarId_clear(x_3, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec_ref(x_283);
x_285 = lean_st_ref_take(x_5);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_285, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 4, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_286);
lean_ctor_set(x_290, 2, x_287);
lean_ctor_set(x_290, 3, x_288);
x_291 = lean_st_ref_set(x_5, x_290);
x_292 = lean_box(0);
x_293 = lean_apply_7(x_2, x_292, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_283, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_295 = x_283;
} else {
 lean_dec_ref(x_283);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
block_278:
{
if (x_270 == 0)
{
lean_dec(x_267);
x_222 = x_5;
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = lean_box(0);
goto block_261;
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_221);
lean_dec(x_13);
lean_dec(x_3);
x_271 = l_Lean_Expr_fvarId_x21(x_267);
lean_dec(x_267);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_272 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(x_11, x_271, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
x_274 = lean_apply_7(x_2, x_273, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
}
}
else
{
lean_dec(x_267);
lean_dec(x_221);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_268;
}
}
else
{
lean_dec(x_263);
x_222 = x_5;
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = lean_box(0);
goto block_261;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_221);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_297 = lean_ctor_get(x_262, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_298 = x_262;
} else {
 lean_dec_ref(x_262);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
block_261:
{
lean_object* x_228; 
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
x_228 = l_Lean_Meta_matchHEq_x3f(x_221, x_223, x_224, x_225, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
if (lean_obj_tag(x_229) == 1)
{
uint8_t x_230; lean_object* x_231; 
lean_dec_ref(x_229);
x_230 = 1;
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
lean_inc(x_11);
lean_inc(x_3);
x_231 = l_Lean_Meta_heqToEq(x_3, x_11, x_230, x_223, x_224, x_225, x_226);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = l_Lean_instBEqMVarId_beq(x_234, x_3);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_237 = lean_st_ref_take(x_222);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 3);
lean_inc(x_240);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 x_241 = x_237;
} else {
 lean_dec_ref(x_237);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_235;
 lean_ctor_set_tag(x_242, 1);
}
lean_ctor_set(x_242, 0, x_233);
lean_ctor_set(x_242, 1, x_239);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 4, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_238);
lean_ctor_set(x_243, 2, x_242);
lean_ctor_set(x_243, 3, x_240);
x_244 = lean_st_ref_set(x_222, x_243);
x_245 = lean_box(0);
x_246 = lean_apply_7(x_2, x_245, x_222, x_223, x_224, x_225, x_226, lean_box(0));
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
x_247 = lean_box(1);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
lean_inc(x_3);
x_248 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(x_3, x_247, x_223, x_224, x_225, x_226);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = lean_unbox(x_249);
lean_dec(x_249);
if (x_251 == 0)
{
lean_dec(x_250);
x_40 = x_222;
x_41 = x_223;
x_42 = x_224;
x_43 = x_225;
x_44 = x_226;
x_45 = lean_box(0);
goto block_92;
}
else
{
uint8_t x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = 0;
x_253 = lean_box(x_252);
if (lean_is_scalar(x_250)) {
 x_254 = lean_alloc_ctor(0, 1, 0);
} else {
 x_254 = x_250;
}
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
}
else
{
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_248;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_255 = lean_ctor_get(x_231, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_256 = x_231;
} else {
 lean_dec_ref(x_231);
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
lean_dec(x_229);
x_40 = x_222;
x_41 = x_223;
x_42 = x_224;
x_43 = x_225;
x_44 = x_226;
x_45 = lean_box(0);
goto block_92;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_258 = lean_ctor_get(x_228, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_259 = x_228;
} else {
 lean_dec_ref(x_228);
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
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_300 = lean_ctor_get(x_220, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_301 = x_220;
} else {
 lean_dec_ref(x_220);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
block_39:
{
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec_ref(x_16);
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
x_28 = lean_apply_7(x_2, x_27, x_19, x_14, x_20, x_18, x_17, lean_box(0));
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
x_37 = lean_apply_7(x_2, x_36, x_19, x_14, x_20, x_18, x_17, lean_box(0));
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_2);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_16);
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
x_15 = lean_box(0);
x_16 = x_89;
x_17 = x_44;
x_18 = x_43;
x_19 = x_40;
x_20 = x_42;
x_21 = x_91;
goto block_39;
}
else
{
x_14 = x_41;
x_15 = lean_box(0);
x_16 = x_89;
x_17 = x_44;
x_18 = x_43;
x_19 = x_40;
x_20 = x_42;
x_21 = x_90;
goto block_39;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_3);
lean_dec(x_1);
x_303 = lean_box(0);
x_304 = lean_apply_7(x_2, x_303, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_304;
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
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed), 7, 0);
return x_1;
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
x_11 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_instBEqFVarId_beq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_5 = lean_st_ref_get(x_3);
x_29 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_29);
lean_dec(x_5);
x_30 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0;
x_31 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_2);
x_32 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_simpH___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
lean_inc_ref(x_1);
x_13 = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(x_1, x_12, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_20 = lean_unbox(x_14);
lean_dec(x_14);
if (x_20 == 0)
{
lean_dec(x_12);
x_15 = x_5;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_array_push(x_5, x_12);
x_15 = x_21;
goto block_19;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_15;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_33 = lean_mk_empty_array_with_capacity(x_3);
x_34 = lean_nat_dec_lt(x_3, x_4);
if (x_34 == 0)
{
lean_dec_ref(x_5);
x_12 = x_33;
x_13 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_4, x_4);
if (x_35 == 0)
{
if (x_34 == 0)
{
lean_dec_ref(x_5);
x_12 = x_33;
x_13 = lean_box(0);
goto block_26;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_4);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(x_5, x_6, x_36, x_37, x_33, x_7, x_8, x_9, x_10);
x_27 = x_38;
goto block_32;
}
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_4);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(x_5, x_6, x_39, x_40, x_33, x_7, x_8, x_9, x_10);
x_27 = x_41;
goto block_32;
}
}
block_26:
{
lean_object* x_14; 
x_14 = l_Lean_MVarId_revert(x_1, x_12, x_2, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
block_32:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_12 = x_28;
x_13 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Meta_Match_simpH___lam__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_MVarId_revert(x_1, x_2, x_3, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_MVarId_getType(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_mk(x_4);
x_16 = l_Array_reverse___redArg(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_box(x_3);
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__1___boxed), 11, 6);
lean_closure_set(x_20, 0, x_12);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_17);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_14);
lean_closure_set(x_20, 5, x_16);
x_21 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_12, x_20, x_5, x_6, x_7, x_8);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_Match_simpH___lam__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static uint64_t _init_l_Lean_Meta_Match_simpH___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Context_config(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint64_t x_21; uint8_t x_22; 
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
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_20 = 1;
lean_ctor_set_uint8(x_8, 9, x_20);
x_21 = l_Lean_Meta_Context_configKey(x_3);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_3, 6);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 5);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_30 = 2;
x_31 = lean_uint64_shift_right(x_21, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_Match_simpH___closed__0;
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_34);
lean_inc_ref(x_12);
lean_ctor_set(x_3, 0, x_35);
lean_inc(x_1);
x_36 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(x_38, 0, x_2);
x_39 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(x_37, x_38, x_39, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_LocalContext_getFVarIds(x_12);
lean_dec_ref(x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_43 = l_Lean_MVarId_tryClearMany(x_1, x_42, x_3, x_4, x_5, x_6);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_46 = l_Lean_Meta_introNCore(x_44, x_41, x_45, x_39, x_39, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_50 = l_Lean_Meta_introNCore(x_49, x_2, x_45, x_39, x_39, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_array_to_list(x_48);
x_55 = lean_array_to_list(x_52);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_45);
x_57 = lean_st_mk_ref(x_56);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_57);
x_58 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_57, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_st_ref_get(x_57);
lean_dec(x_57);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_63 = lean_box(0);
lean_ctor_set(x_58, 0, x_63);
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_58);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
lean_dec(x_61);
x_67 = l_List_reverse___redArg(x_66);
x_68 = lean_array_mk(x_67);
x_69 = lean_box(x_39);
lean_inc(x_64);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(x_70, 0, x_64);
lean_closure_set(x_70, 1, x_68);
lean_closure_set(x_70, 2, x_69);
lean_closure_set(x_70, 3, x_65);
x_71 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_64, x_70, x_3, x_4, x_5, x_6);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_st_ref_get(x_57);
lean_dec(x_57);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_73);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 3);
lean_inc(x_79);
lean_dec(x_73);
x_80 = l_List_reverse___redArg(x_79);
x_81 = lean_array_mk(x_80);
x_82 = lean_box(x_39);
lean_inc(x_77);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(x_83, 0, x_77);
lean_closure_set(x_83, 1, x_81);
lean_closure_set(x_83, 2, x_82);
lean_closure_set(x_83, 3, x_78);
x_84 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_77, x_83, x_3, x_4, x_5, x_6);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_57);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_58);
if (x_85 == 0)
{
return x_58;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_58, 0);
lean_inc(x_86);
lean_dec(x_58);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_48);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_50);
if (x_88 == 0)
{
return x_50;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_50, 0);
lean_inc(x_89);
lean_dec(x_50);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_46);
if (x_91 == 0)
{
return x_46;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_46, 0);
lean_inc(x_92);
lean_dec(x_46);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_41);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_43);
if (x_94 == 0)
{
return x_43;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_43, 0);
lean_inc(x_95);
lean_dec(x_43);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_3);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_40);
if (x_97 == 0)
{
return x_40;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_40, 0);
lean_inc(x_98);
lean_dec(x_40);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_3);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_36);
if (x_100 == 0)
{
return x_36;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_36, 0);
lean_inc(x_101);
lean_dec(x_36);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_103 = 2;
x_104 = lean_uint64_shift_right(x_21, x_103);
x_105 = lean_uint64_shift_left(x_104, x_103);
x_106 = l_Lean_Meta_Match_simpH___closed__0;
x_107 = lean_uint64_lor(x_105, x_106);
x_108 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_108, 0, x_8);
lean_ctor_set_uint64(x_108, sizeof(void*)*1, x_107);
lean_inc_ref(x_12);
x_109 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_11);
lean_ctor_set(x_109, 2, x_12);
lean_ctor_set(x_109, 3, x_13);
lean_ctor_set(x_109, 4, x_14);
lean_ctor_set(x_109, 5, x_15);
lean_ctor_set(x_109, 6, x_16);
lean_ctor_set_uint8(x_109, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 1, x_17);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 2, x_18);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 3, x_19);
lean_inc(x_1);
x_110 = l_Lean_MVarId_getType(x_1, x_109, x_4, x_5, x_6);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_2);
x_112 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(x_112, 0, x_2);
x_113 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_109);
x_114 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(x_111, x_112, x_113, x_109, x_4, x_5, x_6);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_LocalContext_getFVarIds(x_12);
lean_dec_ref(x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_109);
x_117 = l_Lean_MVarId_tryClearMany(x_1, x_116, x_109, x_4, x_5, x_6);
lean_dec_ref(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_109);
x_120 = l_Lean_Meta_introNCore(x_118, x_115, x_119, x_113, x_113, x_109, x_4, x_5, x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_109);
x_124 = l_Lean_Meta_introNCore(x_123, x_2, x_119, x_113, x_113, x_109, x_4, x_5, x_6);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_array_to_list(x_122);
x_129 = lean_array_to_list(x_126);
x_130 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_119);
x_131 = lean_st_mk_ref(x_130);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_109);
lean_inc(x_131);
x_132 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_131, x_109, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_st_ref_get(x_131);
lean_dec(x_131);
x_136 = lean_unbox(x_133);
lean_dec(x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_135);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_137 = lean_box(0);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_134);
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 3);
lean_inc(x_141);
lean_dec(x_135);
x_142 = l_List_reverse___redArg(x_141);
x_143 = lean_array_mk(x_142);
x_144 = lean_box(x_113);
lean_inc(x_139);
x_145 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(x_145, 0, x_139);
lean_closure_set(x_145, 1, x_143);
lean_closure_set(x_145, 2, x_144);
lean_closure_set(x_145, 3, x_140);
x_146 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_139, x_145, x_109, x_4, x_5, x_6);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_148 = x_132;
} else {
 lean_dec_ref(x_132);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_122);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_150 = lean_ctor_get(x_124, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_151 = x_124;
} else {
 lean_dec_ref(x_124);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_153 = lean_ctor_get(x_120, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_154 = x_120;
} else {
 lean_dec_ref(x_120);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_156 = lean_ctor_get(x_117, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_157 = x_117;
} else {
 lean_dec_ref(x_117);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_109);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_114, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_160 = x_114;
} else {
 lean_dec_ref(x_114);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_109);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_110, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_163 = x_110;
} else {
 lean_dec_ref(x_110);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
}
else
{
uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; uint64_t x_195; lean_object* x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; uint64_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_165 = lean_ctor_get_uint8(x_8, 0);
x_166 = lean_ctor_get_uint8(x_8, 1);
x_167 = lean_ctor_get_uint8(x_8, 2);
x_168 = lean_ctor_get_uint8(x_8, 3);
x_169 = lean_ctor_get_uint8(x_8, 4);
x_170 = lean_ctor_get_uint8(x_8, 5);
x_171 = lean_ctor_get_uint8(x_8, 6);
x_172 = lean_ctor_get_uint8(x_8, 7);
x_173 = lean_ctor_get_uint8(x_8, 8);
x_174 = lean_ctor_get_uint8(x_8, 10);
x_175 = lean_ctor_get_uint8(x_8, 11);
x_176 = lean_ctor_get_uint8(x_8, 12);
x_177 = lean_ctor_get_uint8(x_8, 13);
x_178 = lean_ctor_get_uint8(x_8, 14);
x_179 = lean_ctor_get_uint8(x_8, 15);
x_180 = lean_ctor_get_uint8(x_8, 16);
x_181 = lean_ctor_get_uint8(x_8, 17);
x_182 = lean_ctor_get_uint8(x_8, 18);
lean_dec(x_8);
x_183 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_184 = lean_ctor_get(x_3, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_3, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_3, 5);
lean_inc(x_188);
x_189 = lean_ctor_get(x_3, 6);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_191 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_192 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_193 = 1;
x_194 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_194, 0, x_165);
lean_ctor_set_uint8(x_194, 1, x_166);
lean_ctor_set_uint8(x_194, 2, x_167);
lean_ctor_set_uint8(x_194, 3, x_168);
lean_ctor_set_uint8(x_194, 4, x_169);
lean_ctor_set_uint8(x_194, 5, x_170);
lean_ctor_set_uint8(x_194, 6, x_171);
lean_ctor_set_uint8(x_194, 7, x_172);
lean_ctor_set_uint8(x_194, 8, x_173);
lean_ctor_set_uint8(x_194, 9, x_193);
lean_ctor_set_uint8(x_194, 10, x_174);
lean_ctor_set_uint8(x_194, 11, x_175);
lean_ctor_set_uint8(x_194, 12, x_176);
lean_ctor_set_uint8(x_194, 13, x_177);
lean_ctor_set_uint8(x_194, 14, x_178);
lean_ctor_set_uint8(x_194, 15, x_179);
lean_ctor_set_uint8(x_194, 16, x_180);
lean_ctor_set_uint8(x_194, 17, x_181);
lean_ctor_set_uint8(x_194, 18, x_182);
x_195 = l_Lean_Meta_Context_configKey(x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_196 = x_3;
} else {
 lean_dec_ref(x_3);
 x_196 = lean_box(0);
}
x_197 = 2;
x_198 = lean_uint64_shift_right(x_195, x_197);
x_199 = lean_uint64_shift_left(x_198, x_197);
x_200 = l_Lean_Meta_Match_simpH___closed__0;
x_201 = lean_uint64_lor(x_199, x_200);
x_202 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_202, 0, x_194);
lean_ctor_set_uint64(x_202, sizeof(void*)*1, x_201);
lean_inc_ref(x_185);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 7, 4);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_184);
lean_ctor_set(x_203, 2, x_185);
lean_ctor_set(x_203, 3, x_186);
lean_ctor_set(x_203, 4, x_187);
lean_ctor_set(x_203, 5, x_188);
lean_ctor_set(x_203, 6, x_189);
lean_ctor_set_uint8(x_203, sizeof(void*)*7, x_183);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 1, x_190);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 2, x_191);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 3, x_192);
lean_inc(x_1);
x_204 = l_Lean_MVarId_getType(x_1, x_203, x_4, x_5, x_6);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
lean_inc(x_2);
x_206 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(x_206, 0, x_2);
x_207 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_203);
x_208 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(x_205, x_206, x_207, x_203, x_4, x_5, x_6);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l_Lean_LocalContext_getFVarIds(x_185);
lean_dec_ref(x_185);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_203);
x_211 = l_Lean_MVarId_tryClearMany(x_1, x_210, x_203, x_4, x_5, x_6);
lean_dec_ref(x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_203);
x_214 = l_Lean_Meta_introNCore(x_212, x_209, x_213, x_207, x_207, x_203, x_4, x_5, x_6);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_203);
x_218 = l_Lean_Meta_introNCore(x_217, x_2, x_213, x_207, x_207, x_203, x_4, x_5, x_6);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_array_to_list(x_216);
x_223 = lean_array_to_list(x_220);
x_224 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_224, 2, x_223);
lean_ctor_set(x_224, 3, x_213);
x_225 = lean_st_mk_ref(x_224);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_203);
lean_inc(x_225);
x_226 = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(x_225, x_203, x_4, x_5, x_6);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
x_229 = lean_st_ref_get(x_225);
lean_dec(x_225);
x_230 = lean_unbox(x_227);
lean_dec(x_227);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_229);
lean_dec_ref(x_203);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_231 = lean_box(0);
if (lean_is_scalar(x_228)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_228;
}
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_228);
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_229, 3);
lean_inc(x_235);
lean_dec(x_229);
x_236 = l_List_reverse___redArg(x_235);
x_237 = lean_array_mk(x_236);
x_238 = lean_box(x_207);
lean_inc(x_233);
x_239 = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(x_239, 0, x_233);
lean_closure_set(x_239, 1, x_237);
lean_closure_set(x_239, 2, x_238);
lean_closure_set(x_239, 3, x_234);
x_240 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(x_233, x_239, x_203, x_4, x_5, x_6);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_225);
lean_dec_ref(x_203);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_241 = lean_ctor_get(x_226, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_242 = x_226;
} else {
 lean_dec_ref(x_226);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_216);
lean_dec_ref(x_203);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_244 = lean_ctor_get(x_218, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_245 = x_218;
} else {
 lean_dec_ref(x_218);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec_ref(x_203);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_247 = lean_ctor_get(x_214, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_248 = x_214;
} else {
 lean_dec_ref(x_214);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_209);
lean_dec_ref(x_203);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_250 = lean_ctor_get(x_211, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_251 = x_211;
} else {
 lean_dec_ref(x_211);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_203);
lean_dec_ref(x_185);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_208, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_254 = x_208;
} else {
 lean_dec_ref(x_208);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_203);
lean_dec_ref(x_185);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_204, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_257 = x_204;
} else {
 lean_dec_ref(x_204);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_simpH(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = l_Lean_Meta_Match_simpH(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
uint8_t x_16; 
lean_free_object(x_12);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_MVarId_getType(x_17, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_14, 0, x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_14);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_Lean_MVarId_getType(x_26, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = l_Lean_MVarId_getType(x_38, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
return x_12;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
lean_dec(x_12);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_9, 0);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
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
l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0 = _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0);
l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0 = _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0);
l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1 = _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1);
l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2 = _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2);
l_Lean_Meta_Match_simpH___closed__0 = _init_l_Lean_Meta_Match_simpH___closed__0();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
