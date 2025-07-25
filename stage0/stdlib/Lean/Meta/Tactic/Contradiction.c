// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: Lean.Meta.MatchUtil Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1;
static lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1;
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_beqLevelMVarId____x40_Lean_Level___hyg_433____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_hashLevelMVarId____x40_Lean_Level___hyg_491____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
static lean_object* l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM;
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2;
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2;
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__1;
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_contradictionCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1;
static lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
static lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
static lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGenDiseqMask___closed__0;
static lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3;
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0;
x_14 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1;
x_15 = l_Lean_PersistentHashMap_insert___redArg(x_13, x_14, x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_15);
x_16 = lean_st_ref_set(x_3, x_6, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 5);
x_29 = lean_ctor_get(x_7, 6);
x_30 = lean_ctor_get(x_7, 7);
x_31 = lean_ctor_get(x_7, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_32 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0;
x_33 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1;
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_32, x_33, x_30, x_1, x_2);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_6, 0, x_35);
x_36 = lean_st_ref_set(x_3, x_6, x_8);
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_6, 1);
x_42 = lean_ctor_get(x_6, 2);
x_43 = lean_ctor_get(x_6, 3);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_7, 5);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_7, 8);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_54 = x_7;
} else {
 lean_dec_ref(x_7);
 x_54 = lean_box(0);
}
x_55 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0;
x_56 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1;
x_57 = l_Lean_PersistentHashMap_insert___redArg(x_55, x_56, x_52, x_1, x_2);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
x_60 = lean_st_ref_set(x_3, x_59, x_8);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appArg_x21(x_1);
x_6 = l_Lean_Expr_hasLooseBVars(x_5);
lean_dec_ref(x_5);
if (x_6 == 0)
{
return x_4;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed), 1, 0);
x_12 = lean_find_expr(x_11, x_9);
lean_dec(x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
lean_inc(x_1);
x_16 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_3);
x_20 = l_Lean_Meta_mkFalseElim(x_17, x_19, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_21, x_3, x_22);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed), 1, 0);
x_43 = lean_find_expr(x_42, x_40);
lean_dec(x_40);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec_ref(x_43);
lean_inc(x_1);
x_48 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_Expr_appArg_x21(x_47);
lean_dec(x_47);
lean_inc(x_3);
x_52 = l_Lean_Meta_mkFalseElim(x_49, x_51, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_53, x_3, x_54);
lean_dec(x_3);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = 1;
x_59 = lean_box(x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_48, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_67 = x_48;
} else {
 lean_dec_ref(x_48);
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
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_12; 
lean_inc_ref(x_2);
x_12 = l_Lean_FVarId_getType___redArg(x_1, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_5);
x_15 = l_Lean_Meta_whnfD(x_13, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Expr_getAppFn(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_st_ref_get(x_5, x_17);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = l_Lean_Environment_find_x3f(x_24, x_19, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_free_object(x_20);
x_7 = x_23;
goto block_11;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 4);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_List_lengthTR___redArg(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
x_34 = lean_nat_dec_lt(x_32, x_29);
lean_dec(x_29);
x_35 = lean_box(x_34);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; 
lean_dec(x_29);
x_36 = lean_box(x_33);
lean_ctor_set(x_20, 0, x_36);
return x_20;
}
}
else
{
lean_dec(x_27);
lean_free_object(x_20);
x_7 = x_23;
goto block_11;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_39);
lean_dec(x_37);
x_40 = 0;
x_41 = l_Lean_Environment_find_x3f(x_39, x_19, x_40);
if (lean_obj_tag(x_41) == 0)
{
x_7 = x_38;
goto block_11;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
if (lean_obj_tag(x_42) == 5)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
lean_dec_ref(x_42);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 4);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_List_lengthTR___redArg(x_45);
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_nat_dec_lt(x_47, x_44);
lean_dec(x_44);
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
x_52 = lean_box(x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
}
else
{
lean_dec(x_42);
x_7 = x_38;
goto block_11;
}
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_5);
x_7 = x_17;
goto block_11;
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SavedState_restore___redArg(x_1, x_4, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_saveState___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, lean_box(0));
lean_closure_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed), 7, 0);
x_2 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_7, x_6);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_8);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_array_uget(x_5, x_7);
x_25 = l_Lean_Meta_FVarSubst_apply(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_Expr_isFVar(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_inc_ref(x_2);
x_15 = x_2;
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec_ref(x_25);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_27, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec_ref(x_28);
lean_inc_ref(x_2);
x_15 = x_2;
x_16 = x_31;
goto block_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec_ref(x_28);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_33 = l_Lean_Meta_ElimEmptyInductive_elim(x_3, x_27, x_9, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
lean_inc_ref(x_2);
x_15 = x_2;
x_16 = x_36;
goto block_20;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
x_7 = x_18;
x_8 = x_15;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_9, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc_ref(x_2);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_2, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(x_8);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec_ref(x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec_ref(x_17);
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
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec_ref(x_7);
x_16 = lean_array_uget(x_4, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = lean_array_size(x_21);
x_23 = lean_box_usize(x_22);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1;
x_25 = lean_box(x_3);
lean_inc(x_20);
lean_inc_ref(x_1);
x_26 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_20);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_21);
lean_closure_set(x_26, 5, x_23);
lean_closure_set(x_26, 6, x_24);
lean_closure_set(x_26, 7, x_25);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_27 = l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_20, x_26, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 0, x_32);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_28);
lean_free_object(x_16);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec_ref(x_27);
x_37 = 1;
x_38 = lean_usize_add(x_6, x_37);
lean_inc_ref(x_1);
{
size_t _tmp_5 = x_38;
lean_object* _tmp_6 = x_1;
lean_object* _tmp_12 = x_36;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_13 = _tmp_12;
}
goto _start;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_array_size(x_46);
x_48 = lean_box_usize(x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1;
x_50 = lean_box(x_3);
lean_inc(x_45);
lean_inc_ref(x_1);
x_51 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(x_51, 0, x_44);
lean_closure_set(x_51, 1, x_1);
lean_closure_set(x_51, 2, x_45);
lean_closure_set(x_51, 3, x_2);
lean_closure_set(x_51, 4, x_46);
lean_closure_set(x_51, 5, x_48);
lean_closure_set(x_51, 6, x_49);
lean_closure_set(x_51, 7, x_50);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_52 = l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_45, x_51, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_2);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; 
lean_dec(x_53);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_dec_ref(x_52);
x_61 = 1;
x_62 = lean_usize_add(x_6, x_61);
lean_inc_ref(x_1);
{
size_t _tmp_5 = x_62;
lean_object* _tmp_6 = x_1;
lean_object* _tmp_12 = x_60;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_13 = _tmp_12;
}
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec_ref(x_7);
x_16 = lean_array_uget(x_4, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = lean_array_size(x_21);
x_23 = lean_box_usize(x_22);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1;
x_25 = lean_box(x_3);
lean_inc(x_20);
lean_inc_ref(x_1);
x_26 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_20);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_21);
lean_closure_set(x_26, 5, x_23);
lean_closure_set(x_26, 6, x_24);
lean_closure_set(x_26, 7, x_25);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_27 = l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_20, x_26, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 0, x_32);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
lean_dec(x_28);
lean_free_object(x_16);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec_ref(x_27);
x_37 = 1;
x_38 = lean_usize_add(x_6, x_37);
lean_inc_ref(x_1);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_38, x_1, x_8, x_9, x_10, x_11, x_12, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_array_size(x_46);
x_48 = lean_box_usize(x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1;
x_50 = lean_box(x_3);
lean_inc(x_45);
lean_inc_ref(x_1);
x_51 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(x_51, 0, x_44);
lean_closure_set(x_51, 1, x_1);
lean_closure_set(x_51, 2, x_45);
lean_closure_set(x_51, 3, x_2);
lean_closure_set(x_51, 4, x_46);
lean_closure_set(x_51, 5, x_48);
lean_closure_set(x_51, 6, x_49);
lean_closure_set(x_51, 7, x_50);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_52 = l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_45, x_51, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_2);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
lean_dec(x_53);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_dec_ref(x_52);
x_61 = 1;
x_62 = lean_usize_add(x_6, x_61);
lean_inc_ref(x_1);
x_63 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_62, x_1, x_8, x_9, x_10, x_11, x_12, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
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
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
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
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_21; lean_object* x_27; 
x_8 = l_Lean_Meta_saveState___redArg(x_4, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_27 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6, x_30);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_dec(x_28);
x_21 = x_27;
goto block_26;
}
}
else
{
x_21 = x_27;
goto block_26;
}
block_20:
{
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
block_26:
{
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Exception_isInterrupt(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_22);
x_11 = x_21;
x_12 = x_22;
x_13 = x_23;
x_14 = x_25;
goto block_20;
}
else
{
x_11 = x_21;
x_12 = x_22;
x_13 = x_23;
x_14 = x_24;
goto block_20;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("contradiction", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3;
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2;
x_3 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elimEmptyInductive, number subgoals: ", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_MVarId_cases(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_46 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
x_47 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_46, x_8, x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_50;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6;
x_55 = lean_array_get_size(x_12);
x_56 = l_Nat_reprFast(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_58);
lean_ctor_set(x_47, 0, x_54);
x_59 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_46, x_60, x_6, x_7, x_8, x_9, x_52);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_62;
goto block_45;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
lean_dec(x_47);
x_64 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6;
x_65 = lean_array_get_size(x_12);
x_66 = l_Nat_reprFast(x_65);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_46, x_71, x_6, x_7, x_8, x_9, x_63);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_73;
goto block_45;
}
}
block_45:
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_box(0);
x_21 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0;
x_22 = lean_array_size(x_12);
x_23 = 0;
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2(x_21, x_20, x_4, x_12, x_22, x_23, x_21, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_24, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec_ref(x_26);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec_ref(x_26);
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
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_102; 
lean_dec(x_5);
x_74 = lean_ctor_get(x_11, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_76 = x_11;
} else {
 lean_dec_ref(x_11);
 x_76 = lean_box(0);
}
x_102 = l_Lean_Exception_isInterrupt(x_74);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Exception_isRuntime(x_74);
x_77 = x_103;
goto block_101;
}
else
{
x_77 = x_102;
goto block_101;
}
block_101:
{
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_76);
x_78 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
x_79 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_78, x_8, x_75);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_74);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = lean_box(x_4);
lean_ctor_set(x_79, 0, x_84);
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_box(x_4);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec_ref(x_79);
x_89 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7;
x_90 = l_Lean_Exception_toMessageData(x_74);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
x_93 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_78, x_92, x_6, x_7, x_8, x_9, x_88);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_box(x_4);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_box(x_4);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_76)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_76;
}
lean_ctor_set(x_100, 0, x_74);
lean_ctor_set(x_100, 1, x_75);
return x_100;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elimEmptyInductive out-of-fuel", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_st_ref_get(x_3, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_st_ref_take(x_3, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
x_24 = lean_st_ref_set(x_3, x_23, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_ElimEmptyInductive_elim___closed__0;
x_27 = lean_box(x_18);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 10, 4);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_27);
x_29 = l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__7(x_28, x_3, x_4, x_5, x_6, x_7, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
x_31 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_30, x_6, x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_9 = x_34;
goto block_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec_ref(x_31);
x_36 = l_Lean_Meta_ElimEmptyInductive_elim___closed__2;
x_37 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_30, x_36, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_9 = x_38;
goto block_13;
}
}
block_13:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_8);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(x_1, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2(x_1, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_20; lean_object* x_26; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_26 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_29);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_27);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_dec(x_27);
x_20 = x_26;
goto block_25;
}
}
else
{
x_20 = x_26;
goto block_25;
}
block_19:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec_ref(x_10);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
block_25:
{
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
x_10 = x_20;
x_11 = x_21;
x_12 = x_22;
x_13 = x_24;
goto block_19;
}
else
{
x_10 = x_20;
x_11 = x_21;
x_12 = x_22;
x_13 = x_23;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_MVarId_exfalso(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_mk_ref(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_ElimEmptyInductive_elim(x_10, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_dec(x_13);
return x_15;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1), 7, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_expr_has_loose_bvar(x_4, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isEq(x_3);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isHEq(x_3);
x_5 = x_13;
goto block_9;
}
else
{
x_5 = x_12;
goto block_9;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
x_5 = x_14;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_5);
x_7 = lean_array_push(x_2, x_6);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGenDiseqMask___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkGenDiseqMask___closed__0;
x_3 = l_Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_20 = x_5;
} else {
 lean_dec_ref(x_5);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_19, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_21, x_22);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_22, x_33);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_34);
if (x_32 == 0)
{
lean_object* x_35; 
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_20;
}
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_19);
x_11 = x_35;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_86; 
x_36 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_36);
x_86 = lean_infer_type(x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_89 = l_Lean_Meta_matchEq_x3f(x_87, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_91;
goto block_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec_ref(x_89);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 0);
x_97 = lean_ctor_get(x_93, 1);
lean_dec(x_97);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_98 = l_Lean_Meta_mkEqRefl(x_96, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_36);
x_101 = l_Lean_Meta_isExprDefEq(x_36, x_99, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_dec_ref(x_36);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_101, 0);
lean_dec(x_105);
x_106 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
lean_ctor_set(x_93, 1, x_19);
lean_ctor_set(x_93, 0, x_106);
lean_ctor_set(x_101, 0, x_93);
return x_101;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
lean_ctor_set(x_93, 1, x_19);
lean_ctor_set(x_93, 0, x_108);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_free_object(x_93);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec_ref(x_101);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_110;
goto block_85;
}
}
else
{
uint8_t x_111; 
lean_free_object(x_93);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_101);
if (x_111 == 0)
{
return x_101;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_101);
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
lean_free_object(x_93);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_98);
if (x_115 == 0)
{
return x_98;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_98, 0);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_98);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_93, 0);
lean_inc(x_119);
lean_dec(x_93);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_120 = l_Lean_Meta_mkEqRefl(x_119, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_36);
x_123 = l_Lean_Meta_isExprDefEq(x_36, x_121, x_6, x_7, x_8, x_9, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_36);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_19);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
lean_dec_ref(x_123);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_131;
goto block_85;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_132 = lean_ctor_get(x_123, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_134 = x_123;
} else {
 lean_dec_ref(x_123);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_136 = lean_ctor_get(x_120, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_120, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_138 = x_120;
} else {
 lean_dec_ref(x_120);
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
}
}
else
{
uint8_t x_140; 
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_89);
if (x_140 == 0)
{
return x_89;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_89, 0);
x_142 = lean_ctor_get(x_89, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_89);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_86);
if (x_144 == 0)
{
return x_86;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_86, 0);
x_146 = lean_ctor_get(x_86, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_86);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
block_85:
{
lean_object* x_42; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_36);
x_42 = lean_infer_type(x_36, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_45 = l_Lean_Meta_matchHEq_x3f(x_43, x_37, x_38, x_39, x_40, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_19);
x_11 = x_48;
x_12 = x_47;
goto block_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec_ref(x_45);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_53 = l_Lean_Meta_mkHEqRefl(x_52, x_37, x_38, x_39, x_40, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Meta_isExprDefEq(x_36, x_54, x_37, x_38, x_39, x_40, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
if (lean_is_scalar(x_20)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_20;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_19);
lean_ctor_set(x_56, 0, x_62);
return x_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
if (lean_is_scalar(x_20)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_20;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_19);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_dec_ref(x_56);
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_20;
}
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_19);
x_11 = x_68;
x_12 = x_67;
goto block_16;
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
return x_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_56, 0);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_56);
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
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_53);
if (x_73 == 0)
{
return x_53;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_53, 0);
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_53);
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
uint8_t x_77; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_45);
if (x_77 == 0)
{
return x_45;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_45, 0);
x_79 = lean_ctor_get(x_45, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
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
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_42);
if (x_81 == 0)
{
return x_42;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_42, 0);
x_83 = lean_ctor_get(x_42, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_42);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_19);
x_148 = lean_array_fget(x_21, x_22);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_add(x_22, x_150);
lean_dec(x_22);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_21);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_23);
if (x_149 == 0)
{
lean_object* x_153; 
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_20;
}
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_152);
x_11 = x_153;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_201; 
x_154 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_154);
x_201 = lean_infer_type(x_154, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_204 = l_Lean_Meta_matchEq_x3f(x_202, x_6, x_7, x_8, x_9, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_155 = x_6;
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_206;
goto block_200;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
lean_dec_ref(x_205);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_dec_ref(x_204);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_212 = l_Lean_Meta_mkEqRefl(x_210, x_6, x_7, x_8, x_9, x_209);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_154);
x_215 = l_Lean_Meta_isExprDefEq(x_154, x_213, x_6, x_7, x_8, x_9, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec_ref(x_154);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_219 = x_215;
} else {
 lean_dec_ref(x_215);
 x_219 = lean_box(0);
}
x_220 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
if (lean_is_scalar(x_211)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_211;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_152);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
else
{
lean_object* x_223; 
lean_dec(x_211);
x_223 = lean_ctor_get(x_215, 1);
lean_inc(x_223);
lean_dec_ref(x_215);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_155 = x_6;
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_223;
goto block_200;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_211);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_224 = lean_ctor_get(x_215, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_215, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_226 = x_215;
} else {
 lean_dec_ref(x_215);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_211);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_212, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_212, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_230 = x_212;
} else {
 lean_dec_ref(x_212);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_204, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_204, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_234 = x_204;
} else {
 lean_dec_ref(x_204);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_236 = lean_ctor_get(x_201, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_201, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_238 = x_201;
} else {
 lean_dec_ref(x_201);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
block_200:
{
lean_object* x_160; 
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc_ref(x_154);
x_160 = lean_infer_type(x_154, x_155, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
x_163 = l_Lean_Meta_matchHEq_x3f(x_161, x_155, x_156, x_157, x_158, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_20;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_152);
x_11 = x_166;
x_12 = x_165;
goto block_16;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
lean_dec_ref(x_164);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
lean_dec_ref(x_163);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
x_171 = l_Lean_Meta_mkHEqRefl(x_170, x_155, x_156, x_157, x_158, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = l_Lean_Meta_isExprDefEq(x_154, x_172, x_155, x_156, x_157, x_158, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
x_179 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0;
if (lean_is_scalar(x_20)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_20;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_152);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_174, 1);
lean_inc(x_182);
lean_dec_ref(x_174);
lean_inc(x_1);
if (lean_is_scalar(x_20)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_20;
}
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_152);
x_11 = x_183;
x_12 = x_182;
goto block_16;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_184 = lean_ctor_get(x_174, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_186 = x_174;
} else {
 lean_dec_ref(x_174);
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
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_188 = lean_ctor_get(x_171, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_171, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_190 = x_171;
} else {
 lean_dec_ref(x_171);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_192 = lean_ctor_get(x_163, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_163, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_194 = x_163;
} else {
 lean_dec_ref(x_163);
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
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_196 = lean_ctor_get(x_160, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_160, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_198 = x_160;
} else {
 lean_dec_ref(x_160);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
lean_inc_ref(x_7);
x_8 = l_Lean_MetavarContext_getDecl(x_7, x_1);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
lean_inc_ref(x_15);
x_16 = l_Lean_MetavarContext_getDecl(x_15, x_1);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_1, x_3, x_6);
return x_7;
}
}
static lean_object* _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0;
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1;
x_19 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2;
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
x_37 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
lean_inc_ref(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = l_instInhabitedOfMonad___redArg(x_26, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_5(x_47, x_2, x_3, x_4, x_5, x_6);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 2);
x_51 = lean_ctor_get(x_28, 3);
x_52 = lean_ctor_get(x_28, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_53 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
x_54 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
lean_inc_ref(x_49);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_55, 0, x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_59, 0, x_51);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_60, 0, x_50);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_58);
lean_ctor_set(x_26, 1, x_54);
lean_ctor_set(x_26, 0, x_61);
x_62 = 0;
x_63 = lean_box(x_62);
x_64 = l_instInhabitedOfMonad___redArg(x_26, x_63);
x_65 = lean_panic_fn(x_64, x_1);
x_66 = lean_apply_5(x_65, x_2, x_3, x_4, x_5, x_6);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_67 = lean_ctor_get(x_26, 0);
lean_inc(x_67);
lean_dec(x_26);
x_68 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_67, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_67, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_67, 4);
lean_inc_ref(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_73 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
x_74 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
lean_inc_ref(x_68);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_75, 0, x_68);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_68);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_78, 0, x_71);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_79, 0, x_70);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_80, 0, x_69);
if (lean_is_scalar(x_72)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_72;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_73);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_79);
lean_ctor_set(x_81, 4, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = l_instInhabitedOfMonad___redArg(x_82, x_84);
x_86 = lean_panic_fn(x_85, x_1);
x_87 = lean_apply_5(x_86, x_2, x_3, x_4, x_5, x_6);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_88 = lean_ctor_get(x_10, 0);
x_89 = lean_ctor_get(x_10, 2);
x_90 = lean_ctor_get(x_10, 3);
x_91 = lean_ctor_get(x_10, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_10);
x_92 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1;
x_93 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2;
lean_inc_ref(x_88);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_91);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_98, 0, x_90);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_99, 0, x_89);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_98);
lean_ctor_set(x_100, 4, x_97);
lean_ctor_set(x_8, 1, x_93);
lean_ctor_set(x_8, 0, x_100);
x_101 = l_ReaderT_instMonad___redArg(x_8);
x_102 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_102, 2);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_102, 3);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_102, 4);
lean_inc_ref(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
x_109 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
x_110 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
lean_inc_ref(x_104);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_111, 0, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_112, 0, x_104);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_107);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_115, 0, x_106);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_116, 0, x_105);
if (lean_is_scalar(x_108)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_108;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 4, x_114);
if (lean_is_scalar(x_103)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_103;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
x_119 = 0;
x_120 = lean_box(x_119);
x_121 = l_instInhabitedOfMonad___redArg(x_118, x_120);
x_122 = lean_panic_fn(x_121, x_1);
x_123 = lean_apply_5(x_122, x_2, x_3, x_4, x_5, x_6);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_124 = lean_ctor_get(x_8, 0);
lean_inc(x_124);
lean_dec(x_8);
x_125 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_124, 2);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_124, 3);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_124, 4);
lean_inc_ref(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
x_130 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1;
x_131 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2;
lean_inc_ref(x_125);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_132, 0, x_125);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_133, 0, x_125);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_135, 0, x_128);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_136, 0, x_127);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_137, 0, x_126);
if (lean_is_scalar(x_129)) {
 x_138 = lean_alloc_ctor(0, 5, 0);
} else {
 x_138 = x_129;
}
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_130);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_136);
lean_ctor_set(x_138, 4, x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_131);
x_140 = l_ReaderT_instMonad___redArg(x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc_ref(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_141, 2);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_141, 3);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_141, 4);
lean_inc_ref(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
x_148 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3;
x_149 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4;
lean_inc_ref(x_143);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_150, 0, x_143);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_151, 0, x_143);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_153, 0, x_146);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_154, 0, x_145);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_155, 0, x_144);
if (lean_is_scalar(x_147)) {
 x_156 = lean_alloc_ctor(0, 5, 0);
} else {
 x_156 = x_147;
}
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_148);
lean_ctor_set(x_156, 2, x_155);
lean_ctor_set(x_156, 3, x_154);
lean_ctor_set(x_156, 4, x_153);
if (lean_is_scalar(x_142)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_142;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
x_158 = 0;
x_159 = lean_box(x_158);
x_160 = l_instInhabitedOfMonad___redArg(x_157, x_159);
x_161 = lean_panic_fn(x_160, x_1);
x_162 = lean_apply_5(x_161, x_2, x_3, x_4, x_5, x_6);
return x_162;
}
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqLevelMVarId____x40_Lean_Level___hyg_433____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashLevelMVarId____x40_Lean_Level___hyg_491____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(443u);
x_4 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3;
x_5 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_14);
lean_dec_ref(x_9);
x_15 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0;
x_16 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1;
x_17 = l_Lean_PersistentHashMap_find_x3f___redArg(x_15, x_16, x_14, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_free_object(x_7);
x_18 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5;
x_19 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4(x_18, x_2, x_3, x_4, x_5, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = lean_nat_dec_le(x_13, x_20);
lean_dec(x_20);
lean_dec(x_13);
x_22 = lean_box(x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_25);
lean_dec_ref(x_9);
x_26 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0;
x_27 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1;
x_28 = l_Lean_PersistentHashMap_find_x3f___redArg(x_26, x_27, x_25, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_29 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5;
x_30 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4(x_29, x_2, x_3, x_4, x_5, x_23);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_nat_dec_le(x_24, x_31);
lean_dec(x_31);
lean_dec(x_24);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_Level_hasMVar(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
else
{
x_1 = x_26;
goto _start;
}
}
case 2:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec_ref(x_1);
x_16 = x_31;
x_17 = x_32;
goto block_25;
}
case 3:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec_ref(x_1);
x_16 = x_33;
x_17 = x_34;
goto block_25;
}
case 5:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4(x_35, x_2, x_3, x_4, x_5, x_6);
return x_36;
}
default: 
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_Level_hasMVar(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
x_1 = x_7;
x_6 = x_10;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
block_25:
{
uint8_t x_18; 
x_18 = l_Lean_Level_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_7 = x_17;
x_8 = x_20;
x_9 = x_18;
x_10 = x_6;
goto block_15;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_7 = x_17;
x_8 = x_21;
x_9 = x_24;
x_10 = x_23;
goto block_15;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_1 = x_11;
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_26, x_3, x_6);
lean_dec(x_3);
return x_27;
}
case 3:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_28, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec_ref(x_1);
x_31 = l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__7(x_30, x_2, x_3, x_4, x_5, x_6);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_42; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_42 = l_Lean_Expr_hasMVar(x_32);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_32);
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_6);
x_34 = x_44;
x_35 = x_42;
x_36 = x_6;
goto block_41;
}
else
{
lean_object* x_45; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_45 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_34 = x_45;
x_35 = x_48;
x_36 = x_47;
goto block_41;
}
else
{
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_45;
}
}
block_41:
{
if (x_35 == 0)
{
uint8_t x_37; 
lean_dec_ref(x_34);
x_37 = l_Lean_Expr_hasMVar(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
x_1 = x_33;
x_6 = x_36;
goto _start;
}
}
else
{
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
}
case 6:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_16 = x_49;
x_17 = x_50;
goto block_25;
}
case 7:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_16 = x_51;
x_17 = x_52;
goto block_25;
}
case 8:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_75; 
x_53 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_55);
lean_dec_ref(x_1);
x_75 = l_Lean_Expr_hasMVar(x_53);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_53);
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
x_64 = x_77;
x_65 = x_75;
x_66 = x_6;
goto block_74;
}
else
{
lean_object* x_78; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_78 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_53, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_64 = x_78;
x_65 = x_81;
x_66 = x_80;
goto block_74;
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_78;
}
}
block_63:
{
if (x_57 == 0)
{
uint8_t x_59; 
lean_dec_ref(x_56);
x_59 = l_Lean_Expr_hasMVar(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_55);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
x_1 = x_55;
x_6 = x_58;
goto _start;
}
}
else
{
lean_dec_ref(x_55);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_56;
}
}
block_74:
{
if (x_65 == 0)
{
uint8_t x_67; 
lean_dec_ref(x_64);
x_67 = l_Lean_Expr_hasMVar(x_54);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_54);
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_56 = x_69;
x_57 = x_67;
x_58 = x_66;
goto block_63;
}
else
{
lean_object* x_70; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_70 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_54, x_2, x_3, x_4, x_5, x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_56 = x_70;
x_57 = x_73;
x_58 = x_72;
goto block_63;
}
else
{
lean_dec_ref(x_55);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_70;
}
}
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_64;
}
}
}
case 10:
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_82);
lean_dec_ref(x_1);
x_83 = l_Lean_Expr_hasMVar(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_82);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_6);
return x_85;
}
else
{
x_1 = x_82;
goto _start;
}
}
case 11:
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_87);
lean_dec_ref(x_1);
x_88 = l_Lean_Expr_hasMVar(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_87);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_6);
return x_90;
}
else
{
x_1 = x_87;
goto _start;
}
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_6);
return x_94;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_Expr_hasMVar(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
x_1 = x_7;
x_6 = x_10;
goto _start;
}
}
else
{
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
block_25:
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_7 = x_17;
x_8 = x_20;
x_9 = x_18;
x_10 = x_6;
goto block_15;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_7 = x_17;
x_8 = x_21;
x_9 = x_24;
x_10 = x_23;
goto block_15;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6, x_7);
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
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_forallMetaTelescope(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_dec(x_15);
x_16 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = l_Array_toSubarray___redArg(x_16, x_17, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_array_size(x_14);
x_22 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(x_20, x_14, x_21, x_22, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = l_Lean_LocalDecl_toExpr(x_3);
x_28 = l_Lean_mkAppN(x_27, x_14);
lean_dec(x_14);
x_29 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_28, x_6, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_30);
x_32 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_30, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = l_Lean_MVarId_getType(x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Meta_mkFalseElim(x_37, x_30, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_51 = !lean_is_exclusive(x_36);
if (x_51 == 0)
{
return x_36;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_36);
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
lean_dec(x_30);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_32, 0, x_57);
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_32);
if (x_61 == 0)
{
return x_32;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_32, 0);
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_32);
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
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_65 = !lean_is_exclusive(x_23);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_23, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_25, 0);
lean_inc(x_67);
lean_dec_ref(x_25);
lean_ctor_set(x_23, 0, x_67);
return x_23;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_23, 1);
lean_inc(x_68);
lean_dec(x_23);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
lean_dec_ref(x_25);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_71 = !lean_is_exclusive(x_23);
if (x_71 == 0)
{
return x_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
lean_dec(x_11);
x_76 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get_size(x_76);
x_79 = l_Array_toSubarray___redArg(x_76, x_77, x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_size(x_75);
x_83 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_84 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(x_80, x_75, x_82, x_83, x_81, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = l_Lean_LocalDecl_toExpr(x_3);
x_89 = l_Lean_mkAppN(x_88, x_75);
lean_dec(x_75);
x_90 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_89, x_6, x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_91);
x_93 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_91, x_5, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec_ref(x_93);
x_97 = l_Lean_MVarId_getType(x_4, x_5, x_6, x_7, x_8, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = l_Lean_Meta_mkFalseElim(x_98, x_91, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_101);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_108 = x_100;
} else {
 lean_dec_ref(x_100);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_110 = lean_ctor_get(x_97, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_97, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_112 = x_97;
} else {
 lean_dec_ref(x_97);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_114 = lean_ctor_get(x_93, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_115 = x_93;
} else {
 lean_dec_ref(x_93);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_118 = lean_ctor_get(x_93, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_93, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_120 = x_93;
} else {
 lean_dec_ref(x_93);
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
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_122 = lean_ctor_get(x_84, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_123 = x_84;
} else {
 lean_dec_ref(x_84);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_86, 0);
lean_inc(x_124);
lean_dec_ref(x_86);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_126 = lean_ctor_get(x_84, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_128 = x_84;
} else {
 lean_dec_ref(x_84);
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
}
else
{
uint8_t x_130; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_10);
if (x_130 == 0)
{
return x_10;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_10, 0);
x_132 = lean_ctor_get(x_10, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_10);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Contradiction", 30, 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Contradiction.0.Lean.Meta.processGenDiseq", 67, 67);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: isGenDiseq localDecl.type\n  ", 49, 49);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(119u);
x_4 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_LocalDecl_type(x_2);
lean_inc_ref(x_8);
x_9 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
x_11 = l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_box(x_12);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_1);
x_15 = 0;
lean_inc(x_4);
x_16 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg(x_14, x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(x_15);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec_ref(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec_ref(x_17);
x_26 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_25, x_4, x_24);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(x_9);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__9(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_7, x_9);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_19);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_21, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_10, 0, x_26);
lean_ctor_set(x_22, 0, x_10);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec_ref(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec_ref(x_23);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_31);
lean_ctor_set(x_10, 0, x_6);
x_32 = 1;
x_33 = lean_usize_add(x_9, x_32);
x_9 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_10);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_array_uget(x_7, x_9);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_41 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_40, x_39, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec_ref(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec_ref(x_42);
lean_inc(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_9, x_51);
x_9 = x_52;
x_10 = x_50;
x_15 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
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
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
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
}
}
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3;
x_2 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_decide_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
x_16 = l_Lean_LocalDecl_isImplementationDetail(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_18 = l_Lean_Meta_matchNot_x3f(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; uint8_t x_152; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; uint8_t x_323; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; uint8_t x_332; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; uint8_t x_344; uint8_t x_345; uint8_t x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = 1;
if (lean_obj_tag(x_19) == 0)
{
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_20;
goto block_666;
}
else
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_19, 0);
lean_inc(x_667);
lean_dec_ref(x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_668 = l_Lean_Meta_findLocalDeclWithType_x3f(x_667, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec_ref(x_668);
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_670;
goto block_666;
}
else
{
lean_object* x_671; uint8_t x_672; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_671 = lean_ctor_get(x_668, 1);
lean_inc(x_671);
lean_dec_ref(x_668);
x_672 = !lean_is_exclusive(x_669);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_ctor_get(x_669, 0);
lean_inc(x_1);
x_674 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_671);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec_ref(x_674);
x_677 = l_Lean_LocalDecl_toExpr(x_14);
x_678 = l_Lean_mkFVar(x_673);
x_679 = l_Lean_mkApp(x_677, x_678);
lean_inc(x_8);
x_680 = l_Lean_Meta_mkFalseElim(x_675, x_679, x_7, x_8, x_9, x_10, x_676);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec_ref(x_680);
x_683 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_681, x_8, x_682);
lean_dec(x_8);
x_684 = !lean_is_exclusive(x_683);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_683, 0);
lean_dec(x_685);
x_686 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_2);
lean_ctor_set_tag(x_669, 0);
lean_ctor_set(x_669, 0, x_687);
lean_ctor_set(x_683, 0, x_669);
return x_683;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_688 = lean_ctor_get(x_683, 1);
lean_inc(x_688);
lean_dec(x_683);
x_689 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_2);
lean_ctor_set_tag(x_669, 0);
lean_ctor_set(x_669, 0, x_690);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_669);
lean_ctor_set(x_691, 1, x_688);
return x_691;
}
}
else
{
uint8_t x_692; 
lean_free_object(x_669);
lean_dec(x_8);
lean_dec(x_1);
x_692 = !lean_is_exclusive(x_680);
if (x_692 == 0)
{
return x_680;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_680, 0);
x_694 = lean_ctor_get(x_680, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_680);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
}
else
{
uint8_t x_696; 
lean_free_object(x_669);
lean_dec(x_673);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_696 = !lean_is_exclusive(x_674);
if (x_696 == 0)
{
return x_674;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_674, 0);
x_698 = lean_ctor_get(x_674, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_674);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_669, 0);
lean_inc(x_700);
lean_dec(x_669);
lean_inc(x_1);
x_701 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_671);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec_ref(x_701);
x_704 = l_Lean_LocalDecl_toExpr(x_14);
x_705 = l_Lean_mkFVar(x_700);
x_706 = l_Lean_mkApp(x_704, x_705);
lean_inc(x_8);
x_707 = l_Lean_Meta_mkFalseElim(x_702, x_706, x_7, x_8, x_9, x_10, x_703);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec_ref(x_707);
x_710 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_708, x_8, x_709);
lean_dec(x_8);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_712 = x_710;
} else {
 lean_dec_ref(x_710);
 x_712 = lean_box(0);
}
x_713 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_2);
x_715 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_715, 0, x_714);
if (lean_is_scalar(x_712)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_712;
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_711);
return x_716;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_8);
lean_dec(x_1);
x_717 = lean_ctor_get(x_707, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_707, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_719 = x_707;
} else {
 lean_dec_ref(x_707);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_717);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_700);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_721 = lean_ctor_get(x_701, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_701, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_723 = x_701;
} else {
 lean_dec_ref(x_701);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
}
}
else
{
uint8_t x_725; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_725 = !lean_is_exclusive(x_668);
if (x_725 == 0)
{
return x_668;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_668, 0);
x_727 = lean_ctor_get(x_668, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_668);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
block_53:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec_ref(x_3);
x_29 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_30 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_1, x_29, x_28, x_24, x_23, x_25, x_26, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
if (lean_is_scalar(x_15)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_15;
}
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
if (lean_is_scalar(x_15)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_15;
}
lean_ctor_set(x_37, 0, x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_4);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_15;
 lean_ctor_set_tag(x_43, 0);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_15;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec_ref(x_4);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_62:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_1);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_4);
if (lean_is_scalar(x_21)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_21;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_dec(x_21);
x_23 = x_54;
x_24 = x_55;
x_25 = x_56;
x_26 = x_57;
x_27 = x_58;
goto block_53;
}
}
block_69:
{
if (x_68 == 0)
{
lean_dec(x_21);
x_23 = x_63;
x_24 = x_64;
x_25 = x_65;
x_26 = x_66;
x_27 = x_67;
goto block_53;
}
else
{
x_54 = x_63;
x_55 = x_64;
x_56 = x_65;
x_57 = x_66;
x_58 = x_67;
x_59 = x_16;
goto block_62;
}
}
block_77:
{
if (x_76 == 0)
{
x_54 = x_70;
x_55 = x_71;
x_56 = x_72;
x_57 = x_73;
x_58 = x_74;
x_59 = x_16;
goto block_62;
}
else
{
x_63 = x_70;
x_64 = x_71;
x_65 = x_72;
x_66 = x_73;
x_67 = x_74;
x_68 = x_75;
goto block_69;
}
}
block_86:
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_85 == 0)
{
x_70 = x_81;
x_71 = x_80;
x_72 = x_82;
x_73 = x_83;
x_74 = x_84;
x_75 = x_79;
x_76 = x_16;
goto block_77;
}
else
{
if (x_78 == 0)
{
x_63 = x_81;
x_64 = x_80;
x_65 = x_82;
x_66 = x_83;
x_67 = x_84;
x_68 = x_79;
goto block_69;
}
else
{
x_70 = x_81;
x_71 = x_80;
x_72 = x_82;
x_73 = x_83;
x_74 = x_84;
x_75 = x_79;
x_76 = x_16;
goto block_77;
}
}
}
block_113:
{
if (x_94 == 0)
{
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_89;
x_82 = x_90;
x_83 = x_88;
x_84 = x_87;
goto block_86;
}
else
{
lean_object* x_95; 
lean_inc(x_88);
lean_inc_ref(x_90);
lean_inc(x_89);
lean_inc_ref(x_93);
lean_inc(x_14);
lean_inc(x_1);
x_95 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_1, x_14, x_93, x_89, x_90, x_88, x_87);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec_ref(x_95);
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_89;
x_82 = x_90;
x_83 = x_88;
x_84 = x_98;
goto block_86;
}
else
{
uint8_t x_99; 
lean_dec_ref(x_93);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_95, 0);
lean_dec(x_100);
x_101 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_dec(x_95);
x_105 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_2);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_93);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
return x_95;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_95, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_95);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_123:
{
uint8_t x_121; 
x_121 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
if (x_121 == 0)
{
lean_dec_ref(x_17);
x_87 = x_120;
x_88 = x_119;
x_89 = x_117;
x_90 = x_118;
x_91 = x_114;
x_92 = x_115;
x_93 = x_116;
x_94 = x_16;
goto block_113;
}
else
{
uint8_t x_122; 
x_122 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_17);
x_87 = x_120;
x_88 = x_119;
x_89 = x_117;
x_90 = x_118;
x_91 = x_114;
x_92 = x_115;
x_93 = x_116;
x_94 = x_122;
goto block_113;
}
}
block_134:
{
if (x_132 == 0)
{
lean_dec_ref(x_126);
x_114 = x_128;
x_115 = x_131;
x_116 = x_127;
x_117 = x_125;
x_118 = x_130;
x_119 = x_124;
x_120 = x_129;
goto block_123;
}
else
{
lean_object* x_133; 
lean_dec_ref(x_130);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_126);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
}
block_145:
{
uint8_t x_143; 
x_143 = l_Lean_Exception_isInterrupt(x_141);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = l_Lean_Exception_isRuntime(x_141);
x_124 = x_135;
x_125 = x_136;
x_126 = x_141;
x_127 = x_137;
x_128 = x_138;
x_129 = x_142;
x_130 = x_139;
x_131 = x_140;
x_132 = x_144;
goto block_134;
}
else
{
x_124 = x_135;
x_125 = x_136;
x_126 = x_141;
x_127 = x_137;
x_128 = x_138;
x_129 = x_142;
x_130 = x_139;
x_131 = x_140;
x_132 = x_143;
goto block_134;
}
}
block_306:
{
lean_object* x_153; 
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc_ref(x_149);
lean_inc_ref(x_17);
x_153 = l_Lean_Meta_mkDecide(x_17, x_149, x_148, x_151, x_147, x_146);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = l_Lean_Meta_Context_config(x_149);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_158 = lean_ctor_get_uint8(x_149, sizeof(void*)*7);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_149, 2);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_149, 3);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_149, 4);
lean_inc(x_162);
x_163 = lean_ctor_get(x_149, 5);
lean_inc(x_163);
x_164 = lean_ctor_get(x_149, 6);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_149, sizeof(void*)*7 + 1);
x_166 = lean_ctor_get_uint8(x_149, sizeof(void*)*7 + 2);
x_167 = 1;
lean_ctor_set_uint8(x_156, 9, x_167);
x_168 = l_Lean_Meta_Context_configKey(x_149);
x_169 = 2;
x_170 = lean_uint64_shift_right(x_168, x_169);
x_171 = lean_uint64_shift_left(x_170, x_169);
x_172 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_173 = lean_uint64_lor(x_171, x_172);
x_174 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_174, 0, x_156);
lean_ctor_set_uint64(x_174, sizeof(void*)*1, x_173);
x_175 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_159);
lean_ctor_set(x_175, 2, x_160);
lean_ctor_set(x_175, 3, x_161);
lean_ctor_set(x_175, 4, x_162);
lean_ctor_set(x_175, 5, x_163);
lean_ctor_set(x_175, 6, x_164);
lean_ctor_set_uint8(x_175, sizeof(void*)*7, x_158);
lean_ctor_set_uint8(x_175, sizeof(void*)*7 + 1, x_165);
lean_ctor_set_uint8(x_175, sizeof(void*)*7 + 2, x_166);
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc(x_154);
x_176 = lean_whnf(x_154, x_175, x_148, x_151, x_147, x_155);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_180 = l_Lean_Expr_isConstOf(x_177, x_179);
lean_dec(x_177);
if (x_180 == 0)
{
lean_dec(x_154);
x_114 = x_150;
x_115 = x_152;
x_116 = x_149;
x_117 = x_148;
x_118 = x_151;
x_119 = x_147;
x_120 = x_178;
goto block_123;
}
else
{
lean_object* x_181; 
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc_ref(x_149);
lean_inc(x_154);
x_181 = l_Lean_Meta_mkEqRefl(x_154, x_149, x_148, x_151, x_147, x_178);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
lean_inc(x_1);
x_184 = l_Lean_MVarId_getType(x_1, x_149, x_148, x_151, x_147, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_188 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_189 = l_Lean_Expr_getAppNumArgs(x_154);
lean_inc(x_189);
x_190 = lean_mk_array(x_189, x_188);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_sub(x_189, x_191);
lean_dec(x_189);
x_193 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_154, x_190, x_192);
x_194 = lean_array_push(x_193, x_182);
x_195 = l_Lean_mkAppN(x_187, x_194);
lean_dec_ref(x_194);
lean_inc(x_14);
x_196 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc_ref(x_149);
x_197 = l_Lean_Meta_mkAbsurd(x_185, x_196, x_195, x_149, x_148, x_151, x_147, x_186);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
lean_dec_ref(x_151);
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
x_201 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_199, x_148, x_200);
lean_dec(x_148);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 0);
lean_dec(x_203);
x_204 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_197, 1, x_2);
lean_ctor_set(x_197, 0, x_204);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_197);
lean_ctor_set(x_201, 0, x_205);
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_dec(x_201);
x_207 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_197, 1, x_2);
lean_ctor_set(x_197, 0, x_207);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_197);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_210 = lean_ctor_get(x_197, 0);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_197);
x_212 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_210, x_148, x_211);
lean_dec(x_148);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_2);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_214)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_214;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_197, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_197, 1);
lean_inc(x_220);
lean_dec_ref(x_197);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_219;
x_142 = x_220;
goto block_145;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_182);
lean_dec(x_154);
x_221 = lean_ctor_get(x_184, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_184, 1);
lean_inc(x_222);
lean_dec_ref(x_184);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_221;
x_142 = x_222;
goto block_145;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_154);
x_223 = lean_ctor_get(x_181, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_181, 1);
lean_inc(x_224);
lean_dec_ref(x_181);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_223;
x_142 = x_224;
goto block_145;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_154);
x_225 = lean_ctor_get(x_176, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_176, 1);
lean_inc(x_226);
lean_dec_ref(x_176);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_225;
x_142 = x_226;
goto block_145;
}
}
else
{
uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; uint64_t x_256; uint64_t x_257; uint64_t x_258; uint64_t x_259; uint64_t x_260; uint64_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_227 = lean_ctor_get_uint8(x_156, 0);
x_228 = lean_ctor_get_uint8(x_156, 1);
x_229 = lean_ctor_get_uint8(x_156, 2);
x_230 = lean_ctor_get_uint8(x_156, 3);
x_231 = lean_ctor_get_uint8(x_156, 4);
x_232 = lean_ctor_get_uint8(x_156, 5);
x_233 = lean_ctor_get_uint8(x_156, 6);
x_234 = lean_ctor_get_uint8(x_156, 7);
x_235 = lean_ctor_get_uint8(x_156, 8);
x_236 = lean_ctor_get_uint8(x_156, 10);
x_237 = lean_ctor_get_uint8(x_156, 11);
x_238 = lean_ctor_get_uint8(x_156, 12);
x_239 = lean_ctor_get_uint8(x_156, 13);
x_240 = lean_ctor_get_uint8(x_156, 14);
x_241 = lean_ctor_get_uint8(x_156, 15);
x_242 = lean_ctor_get_uint8(x_156, 16);
x_243 = lean_ctor_get_uint8(x_156, 17);
x_244 = lean_ctor_get_uint8(x_156, 18);
lean_dec(x_156);
x_245 = lean_ctor_get_uint8(x_149, sizeof(void*)*7);
x_246 = lean_ctor_get(x_149, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_149, 2);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_149, 3);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_149, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_149, 5);
lean_inc(x_250);
x_251 = lean_ctor_get(x_149, 6);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_149, sizeof(void*)*7 + 1);
x_253 = lean_ctor_get_uint8(x_149, sizeof(void*)*7 + 2);
x_254 = 1;
x_255 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_255, 0, x_227);
lean_ctor_set_uint8(x_255, 1, x_228);
lean_ctor_set_uint8(x_255, 2, x_229);
lean_ctor_set_uint8(x_255, 3, x_230);
lean_ctor_set_uint8(x_255, 4, x_231);
lean_ctor_set_uint8(x_255, 5, x_232);
lean_ctor_set_uint8(x_255, 6, x_233);
lean_ctor_set_uint8(x_255, 7, x_234);
lean_ctor_set_uint8(x_255, 8, x_235);
lean_ctor_set_uint8(x_255, 9, x_254);
lean_ctor_set_uint8(x_255, 10, x_236);
lean_ctor_set_uint8(x_255, 11, x_237);
lean_ctor_set_uint8(x_255, 12, x_238);
lean_ctor_set_uint8(x_255, 13, x_239);
lean_ctor_set_uint8(x_255, 14, x_240);
lean_ctor_set_uint8(x_255, 15, x_241);
lean_ctor_set_uint8(x_255, 16, x_242);
lean_ctor_set_uint8(x_255, 17, x_243);
lean_ctor_set_uint8(x_255, 18, x_244);
x_256 = l_Lean_Meta_Context_configKey(x_149);
x_257 = 2;
x_258 = lean_uint64_shift_right(x_256, x_257);
x_259 = lean_uint64_shift_left(x_258, x_257);
x_260 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_261 = lean_uint64_lor(x_259, x_260);
x_262 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_262, 0, x_255);
lean_ctor_set_uint64(x_262, sizeof(void*)*1, x_261);
x_263 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_246);
lean_ctor_set(x_263, 2, x_247);
lean_ctor_set(x_263, 3, x_248);
lean_ctor_set(x_263, 4, x_249);
lean_ctor_set(x_263, 5, x_250);
lean_ctor_set(x_263, 6, x_251);
lean_ctor_set_uint8(x_263, sizeof(void*)*7, x_245);
lean_ctor_set_uint8(x_263, sizeof(void*)*7 + 1, x_252);
lean_ctor_set_uint8(x_263, sizeof(void*)*7 + 2, x_253);
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc(x_154);
x_264 = lean_whnf(x_154, x_263, x_148, x_151, x_147, x_155);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_268 = l_Lean_Expr_isConstOf(x_265, x_267);
lean_dec(x_265);
if (x_268 == 0)
{
lean_dec(x_154);
x_114 = x_150;
x_115 = x_152;
x_116 = x_149;
x_117 = x_148;
x_118 = x_151;
x_119 = x_147;
x_120 = x_266;
goto block_123;
}
else
{
lean_object* x_269; 
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc_ref(x_149);
lean_inc(x_154);
x_269 = l_Lean_Meta_mkEqRefl(x_154, x_149, x_148, x_151, x_147, x_266);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec_ref(x_269);
lean_inc(x_1);
x_272 = l_Lean_MVarId_getType(x_1, x_149, x_148, x_151, x_147, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_276 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_277 = l_Lean_Expr_getAppNumArgs(x_154);
lean_inc(x_277);
x_278 = lean_mk_array(x_277, x_276);
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_nat_sub(x_277, x_279);
lean_dec(x_277);
x_281 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_154, x_278, x_280);
x_282 = lean_array_push(x_281, x_270);
x_283 = l_Lean_mkAppN(x_275, x_282);
lean_dec_ref(x_282);
lean_inc(x_14);
x_284 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_147);
lean_inc_ref(x_151);
lean_inc(x_148);
lean_inc_ref(x_149);
x_285 = l_Lean_Meta_mkAbsurd(x_273, x_284, x_283, x_149, x_148, x_151, x_147, x_274);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_151);
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_286, x_148, x_287);
lean_dec(x_148);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
x_292 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_288)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_288;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_2);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_291)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_291;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_290);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_285, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
lean_dec_ref(x_285);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_296;
x_142 = x_297;
goto block_145;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_270);
lean_dec(x_154);
x_298 = lean_ctor_get(x_272, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_272, 1);
lean_inc(x_299);
lean_dec_ref(x_272);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_298;
x_142 = x_299;
goto block_145;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_154);
x_300 = lean_ctor_get(x_269, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_269, 1);
lean_inc(x_301);
lean_dec_ref(x_269);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_300;
x_142 = x_301;
goto block_145;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_154);
x_302 = lean_ctor_get(x_264, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_264, 1);
lean_inc(x_303);
lean_dec_ref(x_264);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_302;
x_142 = x_303;
goto block_145;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_153, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_153, 1);
lean_inc(x_305);
lean_dec_ref(x_153);
x_135 = x_147;
x_136 = x_148;
x_137 = x_149;
x_138 = x_150;
x_139 = x_151;
x_140 = x_152;
x_141 = x_304;
x_142 = x_305;
goto block_145;
}
}
block_315:
{
if (x_314 == 0)
{
x_114 = x_311;
x_115 = x_313;
x_116 = x_310;
x_117 = x_309;
x_118 = x_312;
x_119 = x_308;
x_120 = x_307;
goto block_123;
}
else
{
x_146 = x_307;
x_147 = x_308;
x_148 = x_309;
x_149 = x_310;
x_150 = x_311;
x_151 = x_312;
x_152 = x_313;
goto block_306;
}
}
block_325:
{
uint8_t x_324; 
x_324 = l_Lean_Expr_hasFVar(x_317);
lean_dec_ref(x_317);
if (x_324 == 0)
{
x_146 = x_316;
x_147 = x_318;
x_148 = x_319;
x_149 = x_320;
x_150 = x_321;
x_151 = x_322;
x_152 = x_323;
goto block_306;
}
else
{
x_307 = x_316;
x_308 = x_318;
x_309 = x_319;
x_310 = x_320;
x_311 = x_321;
x_312 = x_322;
x_313 = x_323;
x_314 = x_16;
goto block_315;
}
}
block_337:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_inc_ref(x_17);
x_333 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_17, x_328, x_326);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec_ref(x_333);
x_336 = l_Lean_Expr_hasMVar(x_334);
if (x_336 == 0)
{
x_316 = x_335;
x_317 = x_334;
x_318 = x_327;
x_319 = x_328;
x_320 = x_329;
x_321 = x_330;
x_322 = x_331;
x_323 = x_332;
goto block_325;
}
else
{
if (x_16 == 0)
{
lean_dec(x_334);
x_307 = x_335;
x_308 = x_327;
x_309 = x_328;
x_310 = x_329;
x_311 = x_330;
x_312 = x_331;
x_313 = x_332;
x_314 = x_16;
goto block_315;
}
else
{
x_316 = x_335;
x_317 = x_334;
x_318 = x_327;
x_319 = x_328;
x_320 = x_329;
x_321 = x_330;
x_322 = x_331;
x_323 = x_332;
goto block_325;
}
}
}
block_346:
{
if (x_345 == 0)
{
x_114 = x_342;
x_115 = x_344;
x_116 = x_341;
x_117 = x_340;
x_118 = x_343;
x_119 = x_339;
x_120 = x_338;
goto block_123;
}
else
{
x_326 = x_338;
x_327 = x_339;
x_328 = x_340;
x_329 = x_341;
x_330 = x_342;
x_331 = x_343;
x_332 = x_344;
goto block_337;
}
}
block_356:
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_354 == 0)
{
x_338 = x_353;
x_339 = x_352;
x_340 = x_350;
x_341 = x_349;
x_342 = x_347;
x_343 = x_351;
x_344 = x_348;
x_345 = x_16;
goto block_346;
}
else
{
uint8_t x_355; 
x_355 = l_Lean_Expr_hasFVar(x_17);
if (x_355 == 0)
{
x_326 = x_353;
x_327 = x_352;
x_328 = x_350;
x_329 = x_349;
x_330 = x_347;
x_331 = x_351;
x_332 = x_348;
goto block_337;
}
else
{
x_338 = x_353;
x_339 = x_352;
x_340 = x_350;
x_341 = x_349;
x_342 = x_347;
x_343 = x_351;
x_344 = x_348;
x_345 = x_16;
goto block_346;
}
}
}
block_407:
{
lean_object* x_365; 
lean_inc(x_363);
lean_inc_ref(x_361);
lean_inc(x_364);
lean_inc_ref(x_360);
x_365 = l_Lean_Meta_isExprDefEq(x_357, x_359, x_360, x_364, x_361, x_363, x_358);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; uint8_t x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_unbox(x_366);
lean_dec(x_366);
if (x_367 == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec_ref(x_365);
x_347 = x_362;
x_348 = x_22;
x_349 = x_360;
x_350 = x_364;
x_351 = x_361;
x_352 = x_363;
x_353 = x_368;
goto block_356;
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_369 = lean_ctor_get(x_365, 1);
lean_inc(x_369);
lean_dec_ref(x_365);
lean_inc(x_1);
x_370 = l_Lean_MVarId_getType(x_1, x_360, x_364, x_361, x_363, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec_ref(x_370);
x_373 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_363);
lean_inc_ref(x_361);
lean_inc(x_364);
lean_inc_ref(x_360);
x_374 = l_Lean_Meta_mkEqOfHEq(x_373, x_22, x_360, x_364, x_361, x_363, x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec_ref(x_374);
lean_inc(x_364);
x_377 = l_Lean_Meta_mkNoConfusion(x_371, x_375, x_360, x_364, x_361, x_363, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec_ref(x_377);
x_380 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_378, x_364, x_379);
lean_dec(x_364);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_380, 0);
lean_dec(x_382);
x_383 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_2);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_380, 0, x_385);
return x_380;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_386 = lean_ctor_get(x_380, 1);
lean_inc(x_386);
lean_dec(x_380);
x_387 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_2);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_386);
return x_390;
}
}
else
{
uint8_t x_391; 
lean_dec(x_364);
lean_dec(x_1);
x_391 = !lean_is_exclusive(x_377);
if (x_391 == 0)
{
return x_377;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_377, 0);
x_393 = lean_ctor_get(x_377, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_377);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
uint8_t x_395; 
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_363);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_374);
if (x_395 == 0)
{
return x_374;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_374, 0);
x_397 = lean_ctor_get(x_374, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_374);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec(x_14);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_370);
if (x_399 == 0)
{
return x_370;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_370, 0);
x_401 = lean_ctor_get(x_370, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_370);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
}
else
{
uint8_t x_403; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_365);
if (x_403 == 0)
{
return x_365;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_365, 0);
x_405 = lean_ctor_get(x_365, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_365);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
block_452:
{
lean_object* x_414; 
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc_ref(x_17);
x_414 = l_Lean_Meta_matchHEq_x3f(x_17, x_409, x_410, x_411, x_412, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec_ref(x_414);
x_347 = x_408;
x_348 = x_16;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_416;
goto block_356;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
lean_dec_ref(x_415);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
lean_dec_ref(x_414);
x_421 = lean_ctor_get(x_417, 0);
lean_inc(x_421);
lean_dec(x_417);
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
lean_dec(x_418);
x_423 = lean_ctor_get(x_419, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_419, 1);
lean_inc(x_424);
lean_dec(x_419);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
x_425 = l_Lean_Meta_matchConstructorApp_x3f(x_422, x_409, x_410, x_411, x_412, x_420);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_421);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec_ref(x_425);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_427;
goto block_356;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_dec_ref(x_425);
x_429 = lean_ctor_get(x_426, 0);
lean_inc(x_429);
lean_dec_ref(x_426);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
x_430 = l_Lean_Meta_matchConstructorApp_x3f(x_424, x_409, x_410, x_411, x_412, x_428);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
lean_dec(x_429);
lean_dec(x_423);
lean_dec(x_421);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec_ref(x_430);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_432;
goto block_356;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_433 = lean_ctor_get(x_429, 0);
lean_inc_ref(x_433);
lean_dec(x_429);
x_434 = lean_ctor_get(x_431, 0);
lean_inc(x_434);
lean_dec_ref(x_431);
x_435 = lean_ctor_get(x_434, 0);
lean_inc_ref(x_435);
lean_dec(x_434);
x_436 = lean_ctor_get(x_430, 1);
lean_inc(x_436);
lean_dec_ref(x_430);
x_437 = lean_ctor_get(x_433, 0);
lean_inc(x_437);
lean_dec_ref(x_433);
x_438 = lean_ctor_get(x_435, 0);
lean_inc(x_438);
lean_dec_ref(x_435);
x_439 = lean_name_eq(x_437, x_438);
lean_dec(x_438);
lean_dec(x_437);
if (x_439 == 0)
{
x_357 = x_421;
x_358 = x_436;
x_359 = x_423;
x_360 = x_409;
x_361 = x_411;
x_362 = x_408;
x_363 = x_412;
x_364 = x_410;
goto block_407;
}
else
{
if (x_16 == 0)
{
lean_dec(x_423);
lean_dec(x_421);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_436;
goto block_356;
}
else
{
x_357 = x_421;
x_358 = x_436;
x_359 = x_423;
x_360 = x_409;
x_361 = x_411;
x_362 = x_408;
x_363 = x_412;
x_364 = x_410;
goto block_407;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_429);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_430);
if (x_440 == 0)
{
return x_430;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_430, 0);
x_442 = lean_ctor_get(x_430, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_430);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_425);
if (x_444 == 0)
{
return x_425;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_425, 0);
x_446 = lean_ctor_get(x_425, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_425);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_414);
if (x_448 == 0)
{
return x_414;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_414, 0);
x_450 = lean_ctor_get(x_414, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_414);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
block_484:
{
lean_object* x_458; 
lean_inc(x_1);
x_458 = l_Lean_MVarId_getType(x_1, x_453, x_455, x_454, x_456, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec_ref(x_458);
x_461 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_455);
x_462 = l_Lean_Meta_mkNoConfusion(x_459, x_461, x_453, x_455, x_454, x_456, x_460);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_465 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_463, x_455, x_464);
lean_dec(x_455);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_465, 0);
lean_dec(x_467);
x_468 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_2);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_465, 0, x_470);
return x_465;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_471 = lean_ctor_get(x_465, 1);
lean_inc(x_471);
lean_dec(x_465);
x_472 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_2);
x_474 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_471);
return x_475;
}
}
else
{
uint8_t x_476; 
lean_dec(x_455);
lean_dec(x_1);
x_476 = !lean_is_exclusive(x_462);
if (x_476 == 0)
{
return x_462;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_462, 0);
x_478 = lean_ctor_get(x_462, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_462);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_456);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec_ref(x_453);
lean_dec(x_14);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_458);
if (x_480 == 0)
{
return x_458;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_458, 0);
x_482 = lean_ctor_get(x_458, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_458);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
block_525:
{
lean_object* x_490; 
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
lean_inc_ref(x_17);
x_490 = l_Lean_Meta_matchEq_x3f(x_17, x_485, x_486, x_487, x_488, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; 
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
x_408 = x_16;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_492;
goto block_452;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec_ref(x_491);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
lean_dec_ref(x_490);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_494, 1);
lean_inc(x_497);
lean_dec(x_494);
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
x_498 = l_Lean_Meta_matchConstructorApp_x3f(x_496, x_485, x_486, x_487, x_488, x_495);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; 
lean_dec(x_497);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec_ref(x_498);
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_500;
goto block_452;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec_ref(x_498);
x_502 = lean_ctor_get(x_499, 0);
lean_inc(x_502);
lean_dec_ref(x_499);
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
x_503 = l_Lean_Meta_matchConstructorApp_x3f(x_497, x_485, x_486, x_487, x_488, x_501);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
lean_dec(x_502);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec_ref(x_503);
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_505;
goto block_452;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_506 = lean_ctor_get(x_502, 0);
lean_inc_ref(x_506);
lean_dec(x_502);
x_507 = lean_ctor_get(x_504, 0);
lean_inc(x_507);
lean_dec_ref(x_504);
x_508 = lean_ctor_get(x_507, 0);
lean_inc_ref(x_508);
lean_dec(x_507);
x_509 = lean_ctor_get(x_503, 1);
lean_inc(x_509);
lean_dec_ref(x_503);
x_510 = lean_ctor_get(x_506, 0);
lean_inc(x_510);
lean_dec_ref(x_506);
x_511 = lean_ctor_get(x_508, 0);
lean_inc(x_511);
lean_dec_ref(x_508);
x_512 = lean_name_eq(x_510, x_511);
lean_dec(x_511);
lean_dec(x_510);
if (x_512 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_453 = x_485;
x_454 = x_487;
x_455 = x_486;
x_456 = x_488;
x_457 = x_509;
goto block_484;
}
else
{
if (x_16 == 0)
{
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_509;
goto block_452;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_453 = x_485;
x_454 = x_487;
x_455 = x_486;
x_456 = x_488;
x_457 = x_509;
goto block_484;
}
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_502);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_513 = !lean_is_exclusive(x_503);
if (x_513 == 0)
{
return x_503;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_503, 0);
x_515 = lean_ctor_get(x_503, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_503);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_497);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_498);
if (x_517 == 0)
{
return x_498;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_498, 0);
x_519 = lean_ctor_get(x_498, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_498);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_521 = !lean_is_exclusive(x_490);
if (x_521 == 0)
{
return x_490;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_490, 0);
x_523 = lean_ctor_get(x_490, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_490);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
block_666:
{
lean_object* x_531; 
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc_ref(x_17);
x_531 = l_Lean_Meta_matchNe_x3f(x_17, x_526, x_527, x_528, x_529, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec_ref(x_531);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_533;
goto block_525;
}
else
{
uint8_t x_534; 
x_534 = !lean_is_exclusive(x_532);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_535 = lean_ctor_get(x_532, 0);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_ctor_get(x_531, 1);
lean_inc(x_537);
lean_dec_ref(x_531);
x_538 = !lean_is_exclusive(x_536);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_536, 0);
x_540 = lean_ctor_get(x_536, 1);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_539);
x_541 = l_Lean_Meta_isExprDefEq(x_539, x_540, x_526, x_527, x_528, x_529, x_537);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec_ref(x_541);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_544;
goto block_525;
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_545 = lean_ctor_get(x_541, 1);
lean_inc(x_545);
lean_dec_ref(x_541);
lean_inc(x_1);
x_546 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_549 = l_Lean_Meta_mkEqRefl(x_539, x_526, x_527, x_528, x_529, x_548);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec_ref(x_549);
x_552 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_553 = l_Lean_Meta_mkAbsurd(x_547, x_550, x_552, x_526, x_527, x_528, x_529, x_551);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec_ref(x_553);
x_556 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_554, x_527, x_555);
lean_dec(x_527);
x_557 = !lean_is_exclusive(x_556);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_556, 0);
lean_dec(x_558);
x_559 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_536, 1, x_2);
lean_ctor_set(x_536, 0, x_559);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_536);
lean_ctor_set(x_556, 0, x_532);
return x_556;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
lean_dec(x_556);
x_561 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_536, 1, x_2);
lean_ctor_set(x_536, 0, x_561);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_536);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_532);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
}
else
{
uint8_t x_563; 
lean_free_object(x_536);
lean_free_object(x_532);
lean_dec(x_527);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_553);
if (x_563 == 0)
{
return x_553;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_553, 0);
x_565 = lean_ctor_get(x_553, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_553);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_547);
lean_free_object(x_536);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_567 = !lean_is_exclusive(x_549);
if (x_567 == 0)
{
return x_549;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = lean_ctor_get(x_549, 0);
x_569 = lean_ctor_get(x_549, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_549);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
}
else
{
uint8_t x_571; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_571 = !lean_is_exclusive(x_546);
if (x_571 == 0)
{
return x_546;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_546, 0);
x_573 = lean_ctor_get(x_546, 1);
lean_inc(x_573);
lean_inc(x_572);
lean_dec(x_546);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
return x_574;
}
}
}
}
else
{
uint8_t x_575; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_575 = !lean_is_exclusive(x_541);
if (x_575 == 0)
{
return x_541;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_541, 0);
x_577 = lean_ctor_get(x_541, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_541);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_536, 0);
x_580 = lean_ctor_get(x_536, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_536);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_579);
x_581 = l_Lean_Meta_isExprDefEq(x_579, x_580, x_526, x_527, x_528, x_529, x_537);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; uint8_t x_583; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_unbox(x_582);
lean_dec(x_582);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_579);
lean_free_object(x_532);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec_ref(x_581);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_584;
goto block_525;
}
else
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_585 = lean_ctor_get(x_581, 1);
lean_inc(x_585);
lean_dec_ref(x_581);
lean_inc(x_1);
x_586 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec_ref(x_586);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_589 = l_Lean_Meta_mkEqRefl(x_579, x_526, x_527, x_528, x_529, x_588);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec_ref(x_589);
x_592 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_593 = l_Lean_Meta_mkAbsurd(x_587, x_590, x_592, x_526, x_527, x_528, x_529, x_591);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec_ref(x_593);
x_596 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_594, x_527, x_595);
lean_dec(x_527);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
x_599 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_2);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_600);
if (lean_is_scalar(x_598)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_598;
}
lean_ctor_set(x_601, 0, x_532);
lean_ctor_set(x_601, 1, x_597);
return x_601;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_free_object(x_532);
lean_dec(x_527);
lean_dec(x_1);
x_602 = lean_ctor_get(x_593, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_593, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_604 = x_593;
} else {
 lean_dec_ref(x_593);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_603);
return x_605;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_587);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_606 = lean_ctor_get(x_589, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_589, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_608 = x_589;
} else {
 lean_dec_ref(x_589);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_579);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_610 = lean_ctor_get(x_586, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_586, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_612 = x_586;
} else {
 lean_dec_ref(x_586);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_579);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_614 = lean_ctor_get(x_581, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_581, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_616 = x_581;
} else {
 lean_dec_ref(x_581);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_618 = lean_ctor_get(x_532, 0);
lean_inc(x_618);
lean_dec(x_532);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
x_620 = lean_ctor_get(x_531, 1);
lean_inc(x_620);
lean_dec_ref(x_531);
x_621 = lean_ctor_get(x_619, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_623 = x_619;
} else {
 lean_dec_ref(x_619);
 x_623 = lean_box(0);
}
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_621);
x_624 = l_Lean_Meta_isExprDefEq(x_621, x_622, x_526, x_527, x_528, x_529, x_620);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; 
lean_dec(x_623);
lean_dec(x_621);
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
lean_dec_ref(x_624);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_627;
goto block_525;
}
else
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_628 = lean_ctor_get(x_624, 1);
lean_inc(x_628);
lean_dec_ref(x_624);
lean_inc(x_1);
x_629 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec_ref(x_629);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_632 = l_Lean_Meta_mkEqRefl(x_621, x_526, x_527, x_528, x_529, x_631);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec_ref(x_632);
x_635 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_636 = l_Lean_Meta_mkAbsurd(x_630, x_633, x_635, x_526, x_527, x_528, x_529, x_634);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec_ref(x_636);
x_639 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_637, x_527, x_638);
lean_dec(x_527);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_641 = x_639;
} else {
 lean_dec_ref(x_639);
 x_641 = lean_box(0);
}
x_642 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_623)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_623;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_2);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
if (lean_is_scalar(x_641)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_641;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_640);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_623);
lean_dec(x_527);
lean_dec(x_1);
x_646 = lean_ctor_get(x_636, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_636, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_648 = x_636;
} else {
 lean_dec_ref(x_636);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_630);
lean_dec(x_623);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_650 = lean_ctor_get(x_632, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_632, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_652 = x_632;
} else {
 lean_dec_ref(x_632);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_654 = lean_ctor_get(x_629, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_629, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_656 = x_629;
} else {
 lean_dec_ref(x_629);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_654);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_658 = lean_ctor_get(x_624, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_624, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_660 = x_624;
} else {
 lean_dec_ref(x_624);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_531);
if (x_662 == 0)
{
return x_531;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_531, 0);
x_664 = lean_ctor_get(x_531, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_531);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
}
else
{
uint8_t x_729; 
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_729 = !lean_is_exclusive(x_18);
if (x_729 == 0)
{
return x_18;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_18, 0);
x_731 = lean_ctor_get(x_18, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_18);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
else
{
lean_object* x_733; lean_object* x_734; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_15)) {
 x_733 = lean_alloc_ctor(1, 1, 0);
} else {
 x_733 = x_15;
}
lean_ctor_set(x_733, 0, x_4);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_11);
return x_734;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_array_size(x_14);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_15, x_14, x_17, x_18, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_free_object(x_6);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec_ref(x_21);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec_ref(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_6);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_39, x_38, x_41, x_42, x_40, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec_ref(x_45);
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0), 11, 4);
lean_closure_set(x_61, 0, x_2);
lean_closure_set(x_61, 1, x_4);
lean_closure_set(x_61, 2, x_1);
lean_closure_set(x_61, 3, x_3);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
x_64 = lean_array_size(x_60);
x_65 = 0;
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(x_61, x_62, x_60, x_64, x_65, x_63, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
lean_ctor_set(x_6, 0, x_71);
lean_ctor_set(x_66, 0, x_6);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
lean_ctor_set(x_6, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_67);
lean_free_object(x_6);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec_ref(x_68);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
lean_dec_ref(x_68);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_6);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
lean_dec(x_6);
x_86 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0), 11, 4);
lean_closure_set(x_86, 0, x_2);
lean_closure_set(x_86, 1, x_4);
lean_closure_set(x_86, 2, x_1);
lean_closure_set(x_86, 3, x_3);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_7);
x_89 = lean_array_size(x_85);
x_90 = 0;
x_91 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(x_86, x_87, x_85, x_89, x_90, x_88, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec_ref(x_93);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_11 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_39);
x_41 = lean_apply_7(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec_ref(x_42);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_5, x_53);
x_5 = x_54;
x_6 = x_52;
x_11 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
x_16 = l_Lean_LocalDecl_isImplementationDetail(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_18 = l_Lean_Meta_matchNot_x3f(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint8_t x_314; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; uint8_t x_345; uint8_t x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = 1;
if (lean_obj_tag(x_19) == 0)
{
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_20;
goto block_666;
}
else
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_19, 0);
lean_inc(x_667);
lean_dec_ref(x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_668 = l_Lean_Meta_findLocalDeclWithType_x3f(x_667, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec_ref(x_668);
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_670;
goto block_666;
}
else
{
lean_object* x_671; uint8_t x_672; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_671 = lean_ctor_get(x_668, 1);
lean_inc(x_671);
lean_dec_ref(x_668);
x_672 = !lean_is_exclusive(x_669);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_ctor_get(x_669, 0);
lean_inc(x_1);
x_674 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_671);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec_ref(x_674);
x_677 = l_Lean_LocalDecl_toExpr(x_14);
x_678 = l_Lean_mkFVar(x_673);
x_679 = l_Lean_mkApp(x_677, x_678);
lean_inc(x_8);
x_680 = l_Lean_Meta_mkFalseElim(x_675, x_679, x_7, x_8, x_9, x_10, x_676);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec_ref(x_680);
x_683 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_681, x_8, x_682);
lean_dec(x_8);
x_684 = !lean_is_exclusive(x_683);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_683, 0);
lean_dec(x_685);
x_686 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_2);
lean_ctor_set_tag(x_669, 0);
lean_ctor_set(x_669, 0, x_687);
lean_ctor_set(x_683, 0, x_669);
return x_683;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_688 = lean_ctor_get(x_683, 1);
lean_inc(x_688);
lean_dec(x_683);
x_689 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_2);
lean_ctor_set_tag(x_669, 0);
lean_ctor_set(x_669, 0, x_690);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_669);
lean_ctor_set(x_691, 1, x_688);
return x_691;
}
}
else
{
uint8_t x_692; 
lean_free_object(x_669);
lean_dec(x_8);
lean_dec(x_1);
x_692 = !lean_is_exclusive(x_680);
if (x_692 == 0)
{
return x_680;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_680, 0);
x_694 = lean_ctor_get(x_680, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_680);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
}
else
{
uint8_t x_696; 
lean_free_object(x_669);
lean_dec(x_673);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_696 = !lean_is_exclusive(x_674);
if (x_696 == 0)
{
return x_674;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_674, 0);
x_698 = lean_ctor_get(x_674, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_674);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_669, 0);
lean_inc(x_700);
lean_dec(x_669);
lean_inc(x_1);
x_701 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_671);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec_ref(x_701);
x_704 = l_Lean_LocalDecl_toExpr(x_14);
x_705 = l_Lean_mkFVar(x_700);
x_706 = l_Lean_mkApp(x_704, x_705);
lean_inc(x_8);
x_707 = l_Lean_Meta_mkFalseElim(x_702, x_706, x_7, x_8, x_9, x_10, x_703);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec_ref(x_707);
x_710 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_708, x_8, x_709);
lean_dec(x_8);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_712 = x_710;
} else {
 lean_dec_ref(x_710);
 x_712 = lean_box(0);
}
x_713 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_2);
x_715 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_715, 0, x_714);
if (lean_is_scalar(x_712)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_712;
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_711);
return x_716;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_8);
lean_dec(x_1);
x_717 = lean_ctor_get(x_707, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_707, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_719 = x_707;
} else {
 lean_dec_ref(x_707);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_717);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_700);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_721 = lean_ctor_get(x_701, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_701, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_723 = x_701;
} else {
 lean_dec_ref(x_701);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
}
}
else
{
uint8_t x_725; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_725 = !lean_is_exclusive(x_668);
if (x_725 == 0)
{
return x_668;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_668, 0);
x_727 = lean_ctor_get(x_668, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_668);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
block_53:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec_ref(x_3);
x_29 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_30 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_1, x_29, x_28, x_25, x_27, x_23, x_24, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
if (lean_is_scalar(x_15)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_15;
}
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
if (lean_is_scalar(x_15)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_15;
}
lean_ctor_set(x_37, 0, x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_4);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_15;
 lean_ctor_set_tag(x_43, 0);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_15;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec_ref(x_4);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_62:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_58);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_1);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_4);
if (lean_is_scalar(x_21)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_21;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_dec(x_21);
x_23 = x_54;
x_24 = x_55;
x_25 = x_56;
x_26 = x_57;
x_27 = x_58;
goto block_53;
}
}
block_69:
{
if (x_66 == 0)
{
lean_dec(x_21);
x_23 = x_63;
x_24 = x_64;
x_25 = x_65;
x_26 = x_67;
x_27 = x_68;
goto block_53;
}
else
{
x_54 = x_63;
x_55 = x_64;
x_56 = x_65;
x_57 = x_67;
x_58 = x_68;
x_59 = x_16;
goto block_62;
}
}
block_77:
{
if (x_76 == 0)
{
x_54 = x_70;
x_55 = x_71;
x_56 = x_72;
x_57 = x_74;
x_58 = x_75;
x_59 = x_16;
goto block_62;
}
else
{
x_63 = x_70;
x_64 = x_71;
x_65 = x_72;
x_66 = x_73;
x_67 = x_74;
x_68 = x_75;
goto block_69;
}
}
block_86:
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_85 == 0)
{
x_70 = x_82;
x_71 = x_83;
x_72 = x_80;
x_73 = x_79;
x_74 = x_84;
x_75 = x_81;
x_76 = x_16;
goto block_77;
}
else
{
if (x_78 == 0)
{
x_63 = x_82;
x_64 = x_83;
x_65 = x_80;
x_66 = x_79;
x_67 = x_84;
x_68 = x_81;
goto block_69;
}
else
{
x_70 = x_82;
x_71 = x_83;
x_72 = x_80;
x_73 = x_79;
x_74 = x_84;
x_75 = x_81;
x_76 = x_16;
goto block_77;
}
}
}
block_113:
{
if (x_94 == 0)
{
x_78 = x_90;
x_79 = x_91;
x_80 = x_92;
x_81 = x_87;
x_82 = x_93;
x_83 = x_89;
x_84 = x_88;
goto block_86;
}
else
{
lean_object* x_95; 
lean_inc(x_89);
lean_inc_ref(x_93);
lean_inc(x_87);
lean_inc_ref(x_92);
lean_inc(x_14);
lean_inc(x_1);
x_95 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_1, x_14, x_92, x_87, x_93, x_89, x_88);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec_ref(x_95);
x_78 = x_90;
x_79 = x_91;
x_80 = x_92;
x_81 = x_87;
x_82 = x_93;
x_83 = x_89;
x_84 = x_98;
goto block_86;
}
else
{
uint8_t x_99; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_95, 0);
lean_dec(x_100);
x_101 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_dec(x_95);
x_105 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_2);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
return x_95;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_95, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_95);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_123:
{
uint8_t x_121; 
x_121 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
if (x_121 == 0)
{
lean_dec_ref(x_17);
x_87 = x_117;
x_88 = x_120;
x_89 = x_119;
x_90 = x_114;
x_91 = x_115;
x_92 = x_116;
x_93 = x_118;
x_94 = x_16;
goto block_113;
}
else
{
uint8_t x_122; 
x_122 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_17);
x_87 = x_117;
x_88 = x_120;
x_89 = x_119;
x_90 = x_114;
x_91 = x_115;
x_92 = x_116;
x_93 = x_118;
x_94 = x_122;
goto block_113;
}
}
block_134:
{
if (x_132 == 0)
{
lean_dec_ref(x_129);
x_114 = x_125;
x_115 = x_128;
x_116 = x_127;
x_117 = x_124;
x_118 = x_131;
x_119 = x_126;
x_120 = x_130;
goto block_123;
}
else
{
lean_object* x_133; 
lean_dec_ref(x_131);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
}
block_145:
{
uint8_t x_143; 
x_143 = l_Lean_Exception_isInterrupt(x_141);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = l_Lean_Exception_isRuntime(x_141);
x_124 = x_135;
x_125 = x_136;
x_126 = x_138;
x_127 = x_137;
x_128 = x_139;
x_129 = x_141;
x_130 = x_142;
x_131 = x_140;
x_132 = x_144;
goto block_134;
}
else
{
x_124 = x_135;
x_125 = x_136;
x_126 = x_138;
x_127 = x_137;
x_128 = x_139;
x_129 = x_141;
x_130 = x_142;
x_131 = x_140;
x_132 = x_143;
goto block_134;
}
}
block_306:
{
lean_object* x_153; 
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc_ref(x_150);
lean_inc_ref(x_17);
x_153 = l_Lean_Meta_mkDecide(x_17, x_150, x_147, x_152, x_149, x_146);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = l_Lean_Meta_Context_config(x_150);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_158 = lean_ctor_get_uint8(x_150, sizeof(void*)*7);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_150, 2);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_150, 3);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_150, 4);
lean_inc(x_162);
x_163 = lean_ctor_get(x_150, 5);
lean_inc(x_163);
x_164 = lean_ctor_get(x_150, 6);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_150, sizeof(void*)*7 + 1);
x_166 = lean_ctor_get_uint8(x_150, sizeof(void*)*7 + 2);
x_167 = 1;
lean_ctor_set_uint8(x_156, 9, x_167);
x_168 = l_Lean_Meta_Context_configKey(x_150);
x_169 = 2;
x_170 = lean_uint64_shift_right(x_168, x_169);
x_171 = lean_uint64_shift_left(x_170, x_169);
x_172 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_173 = lean_uint64_lor(x_171, x_172);
x_174 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_174, 0, x_156);
lean_ctor_set_uint64(x_174, sizeof(void*)*1, x_173);
x_175 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_159);
lean_ctor_set(x_175, 2, x_160);
lean_ctor_set(x_175, 3, x_161);
lean_ctor_set(x_175, 4, x_162);
lean_ctor_set(x_175, 5, x_163);
lean_ctor_set(x_175, 6, x_164);
lean_ctor_set_uint8(x_175, sizeof(void*)*7, x_158);
lean_ctor_set_uint8(x_175, sizeof(void*)*7 + 1, x_165);
lean_ctor_set_uint8(x_175, sizeof(void*)*7 + 2, x_166);
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc(x_154);
x_176 = lean_whnf(x_154, x_175, x_147, x_152, x_149, x_155);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_180 = l_Lean_Expr_isConstOf(x_177, x_179);
lean_dec(x_177);
if (x_180 == 0)
{
lean_dec(x_154);
x_114 = x_148;
x_115 = x_151;
x_116 = x_150;
x_117 = x_147;
x_118 = x_152;
x_119 = x_149;
x_120 = x_178;
goto block_123;
}
else
{
lean_object* x_181; 
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc_ref(x_150);
lean_inc(x_154);
x_181 = l_Lean_Meta_mkEqRefl(x_154, x_150, x_147, x_152, x_149, x_178);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
lean_inc(x_1);
x_184 = l_Lean_MVarId_getType(x_1, x_150, x_147, x_152, x_149, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_188 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_189 = l_Lean_Expr_getAppNumArgs(x_154);
lean_inc(x_189);
x_190 = lean_mk_array(x_189, x_188);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_sub(x_189, x_191);
lean_dec(x_189);
x_193 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_154, x_190, x_192);
x_194 = lean_array_push(x_193, x_182);
x_195 = l_Lean_mkAppN(x_187, x_194);
lean_dec_ref(x_194);
lean_inc(x_14);
x_196 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc_ref(x_150);
x_197 = l_Lean_Meta_mkAbsurd(x_185, x_196, x_195, x_150, x_147, x_152, x_149, x_186);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
lean_dec_ref(x_152);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
x_201 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_199, x_147, x_200);
lean_dec(x_147);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 0);
lean_dec(x_203);
x_204 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_197, 1, x_2);
lean_ctor_set(x_197, 0, x_204);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_197);
lean_ctor_set(x_201, 0, x_205);
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_dec(x_201);
x_207 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_197, 1, x_2);
lean_ctor_set(x_197, 0, x_207);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_197);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_210 = lean_ctor_get(x_197, 0);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_197);
x_212 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_210, x_147, x_211);
lean_dec(x_147);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_2);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_214)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_214;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_197, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_197, 1);
lean_inc(x_220);
lean_dec_ref(x_197);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_219;
x_142 = x_220;
goto block_145;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_182);
lean_dec(x_154);
x_221 = lean_ctor_get(x_184, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_184, 1);
lean_inc(x_222);
lean_dec_ref(x_184);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_221;
x_142 = x_222;
goto block_145;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_154);
x_223 = lean_ctor_get(x_181, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_181, 1);
lean_inc(x_224);
lean_dec_ref(x_181);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_223;
x_142 = x_224;
goto block_145;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_154);
x_225 = lean_ctor_get(x_176, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_176, 1);
lean_inc(x_226);
lean_dec_ref(x_176);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_225;
x_142 = x_226;
goto block_145;
}
}
else
{
uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; uint64_t x_256; uint64_t x_257; uint64_t x_258; uint64_t x_259; uint64_t x_260; uint64_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_227 = lean_ctor_get_uint8(x_156, 0);
x_228 = lean_ctor_get_uint8(x_156, 1);
x_229 = lean_ctor_get_uint8(x_156, 2);
x_230 = lean_ctor_get_uint8(x_156, 3);
x_231 = lean_ctor_get_uint8(x_156, 4);
x_232 = lean_ctor_get_uint8(x_156, 5);
x_233 = lean_ctor_get_uint8(x_156, 6);
x_234 = lean_ctor_get_uint8(x_156, 7);
x_235 = lean_ctor_get_uint8(x_156, 8);
x_236 = lean_ctor_get_uint8(x_156, 10);
x_237 = lean_ctor_get_uint8(x_156, 11);
x_238 = lean_ctor_get_uint8(x_156, 12);
x_239 = lean_ctor_get_uint8(x_156, 13);
x_240 = lean_ctor_get_uint8(x_156, 14);
x_241 = lean_ctor_get_uint8(x_156, 15);
x_242 = lean_ctor_get_uint8(x_156, 16);
x_243 = lean_ctor_get_uint8(x_156, 17);
x_244 = lean_ctor_get_uint8(x_156, 18);
lean_dec(x_156);
x_245 = lean_ctor_get_uint8(x_150, sizeof(void*)*7);
x_246 = lean_ctor_get(x_150, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_150, 2);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_150, 3);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_150, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_150, 5);
lean_inc(x_250);
x_251 = lean_ctor_get(x_150, 6);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_150, sizeof(void*)*7 + 1);
x_253 = lean_ctor_get_uint8(x_150, sizeof(void*)*7 + 2);
x_254 = 1;
x_255 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_255, 0, x_227);
lean_ctor_set_uint8(x_255, 1, x_228);
lean_ctor_set_uint8(x_255, 2, x_229);
lean_ctor_set_uint8(x_255, 3, x_230);
lean_ctor_set_uint8(x_255, 4, x_231);
lean_ctor_set_uint8(x_255, 5, x_232);
lean_ctor_set_uint8(x_255, 6, x_233);
lean_ctor_set_uint8(x_255, 7, x_234);
lean_ctor_set_uint8(x_255, 8, x_235);
lean_ctor_set_uint8(x_255, 9, x_254);
lean_ctor_set_uint8(x_255, 10, x_236);
lean_ctor_set_uint8(x_255, 11, x_237);
lean_ctor_set_uint8(x_255, 12, x_238);
lean_ctor_set_uint8(x_255, 13, x_239);
lean_ctor_set_uint8(x_255, 14, x_240);
lean_ctor_set_uint8(x_255, 15, x_241);
lean_ctor_set_uint8(x_255, 16, x_242);
lean_ctor_set_uint8(x_255, 17, x_243);
lean_ctor_set_uint8(x_255, 18, x_244);
x_256 = l_Lean_Meta_Context_configKey(x_150);
x_257 = 2;
x_258 = lean_uint64_shift_right(x_256, x_257);
x_259 = lean_uint64_shift_left(x_258, x_257);
x_260 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_261 = lean_uint64_lor(x_259, x_260);
x_262 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_262, 0, x_255);
lean_ctor_set_uint64(x_262, sizeof(void*)*1, x_261);
x_263 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_246);
lean_ctor_set(x_263, 2, x_247);
lean_ctor_set(x_263, 3, x_248);
lean_ctor_set(x_263, 4, x_249);
lean_ctor_set(x_263, 5, x_250);
lean_ctor_set(x_263, 6, x_251);
lean_ctor_set_uint8(x_263, sizeof(void*)*7, x_245);
lean_ctor_set_uint8(x_263, sizeof(void*)*7 + 1, x_252);
lean_ctor_set_uint8(x_263, sizeof(void*)*7 + 2, x_253);
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc(x_154);
x_264 = lean_whnf(x_154, x_263, x_147, x_152, x_149, x_155);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_268 = l_Lean_Expr_isConstOf(x_265, x_267);
lean_dec(x_265);
if (x_268 == 0)
{
lean_dec(x_154);
x_114 = x_148;
x_115 = x_151;
x_116 = x_150;
x_117 = x_147;
x_118 = x_152;
x_119 = x_149;
x_120 = x_266;
goto block_123;
}
else
{
lean_object* x_269; 
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc_ref(x_150);
lean_inc(x_154);
x_269 = l_Lean_Meta_mkEqRefl(x_154, x_150, x_147, x_152, x_149, x_266);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec_ref(x_269);
lean_inc(x_1);
x_272 = l_Lean_MVarId_getType(x_1, x_150, x_147, x_152, x_149, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_276 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_277 = l_Lean_Expr_getAppNumArgs(x_154);
lean_inc(x_277);
x_278 = lean_mk_array(x_277, x_276);
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_nat_sub(x_277, x_279);
lean_dec(x_277);
x_281 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_154, x_278, x_280);
x_282 = lean_array_push(x_281, x_270);
x_283 = l_Lean_mkAppN(x_275, x_282);
lean_dec_ref(x_282);
lean_inc(x_14);
x_284 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_147);
lean_inc_ref(x_150);
x_285 = l_Lean_Meta_mkAbsurd(x_273, x_284, x_283, x_150, x_147, x_152, x_149, x_274);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_152);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_286, x_147, x_287);
lean_dec(x_147);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
x_292 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_288)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_288;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_2);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_291)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_291;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_290);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_285, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
lean_dec_ref(x_285);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_296;
x_142 = x_297;
goto block_145;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_270);
lean_dec(x_154);
x_298 = lean_ctor_get(x_272, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_272, 1);
lean_inc(x_299);
lean_dec_ref(x_272);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_298;
x_142 = x_299;
goto block_145;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_154);
x_300 = lean_ctor_get(x_269, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_269, 1);
lean_inc(x_301);
lean_dec_ref(x_269);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_300;
x_142 = x_301;
goto block_145;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_154);
x_302 = lean_ctor_get(x_264, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_264, 1);
lean_inc(x_303);
lean_dec_ref(x_264);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_302;
x_142 = x_303;
goto block_145;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_153, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_153, 1);
lean_inc(x_305);
lean_dec_ref(x_153);
x_135 = x_147;
x_136 = x_148;
x_137 = x_150;
x_138 = x_149;
x_139 = x_151;
x_140 = x_152;
x_141 = x_304;
x_142 = x_305;
goto block_145;
}
}
block_315:
{
if (x_314 == 0)
{
x_114 = x_309;
x_115 = x_312;
x_116 = x_311;
x_117 = x_308;
x_118 = x_313;
x_119 = x_310;
x_120 = x_307;
goto block_123;
}
else
{
x_146 = x_307;
x_147 = x_308;
x_148 = x_309;
x_149 = x_310;
x_150 = x_311;
x_151 = x_312;
x_152 = x_313;
goto block_306;
}
}
block_325:
{
uint8_t x_324; 
x_324 = l_Lean_Expr_hasFVar(x_316);
lean_dec_ref(x_316);
if (x_324 == 0)
{
x_146 = x_317;
x_147 = x_318;
x_148 = x_319;
x_149 = x_321;
x_150 = x_320;
x_151 = x_322;
x_152 = x_323;
goto block_306;
}
else
{
x_307 = x_317;
x_308 = x_318;
x_309 = x_319;
x_310 = x_321;
x_311 = x_320;
x_312 = x_322;
x_313 = x_323;
x_314 = x_16;
goto block_315;
}
}
block_337:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_inc_ref(x_17);
x_333 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_17, x_326, x_328);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec_ref(x_333);
x_336 = l_Lean_Expr_hasMVar(x_334);
if (x_336 == 0)
{
x_316 = x_334;
x_317 = x_335;
x_318 = x_326;
x_319 = x_327;
x_320 = x_330;
x_321 = x_329;
x_322 = x_331;
x_323 = x_332;
goto block_325;
}
else
{
if (x_16 == 0)
{
lean_dec(x_334);
x_307 = x_335;
x_308 = x_326;
x_309 = x_327;
x_310 = x_329;
x_311 = x_330;
x_312 = x_331;
x_313 = x_332;
x_314 = x_16;
goto block_315;
}
else
{
x_316 = x_334;
x_317 = x_335;
x_318 = x_326;
x_319 = x_327;
x_320 = x_330;
x_321 = x_329;
x_322 = x_331;
x_323 = x_332;
goto block_325;
}
}
}
block_346:
{
if (x_345 == 0)
{
x_114 = x_339;
x_115 = x_343;
x_116 = x_342;
x_117 = x_338;
x_118 = x_344;
x_119 = x_341;
x_120 = x_340;
goto block_123;
}
else
{
x_326 = x_338;
x_327 = x_339;
x_328 = x_340;
x_329 = x_341;
x_330 = x_342;
x_331 = x_343;
x_332 = x_344;
goto block_337;
}
}
block_356:
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_354 == 0)
{
x_338 = x_350;
x_339 = x_347;
x_340 = x_353;
x_341 = x_352;
x_342 = x_349;
x_343 = x_348;
x_344 = x_351;
x_345 = x_16;
goto block_346;
}
else
{
uint8_t x_355; 
x_355 = l_Lean_Expr_hasFVar(x_17);
if (x_355 == 0)
{
x_326 = x_350;
x_327 = x_347;
x_328 = x_353;
x_329 = x_352;
x_330 = x_349;
x_331 = x_348;
x_332 = x_351;
goto block_337;
}
else
{
x_338 = x_350;
x_339 = x_347;
x_340 = x_353;
x_341 = x_352;
x_342 = x_349;
x_343 = x_348;
x_344 = x_351;
x_345 = x_16;
goto block_346;
}
}
}
block_407:
{
lean_object* x_365; 
lean_inc(x_358);
lean_inc_ref(x_362);
lean_inc(x_360);
lean_inc_ref(x_361);
x_365 = l_Lean_Meta_isExprDefEq(x_363, x_357, x_361, x_360, x_362, x_358, x_364);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; uint8_t x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_unbox(x_366);
lean_dec(x_366);
if (x_367 == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec_ref(x_365);
x_347 = x_359;
x_348 = x_22;
x_349 = x_361;
x_350 = x_360;
x_351 = x_362;
x_352 = x_358;
x_353 = x_368;
goto block_356;
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_369 = lean_ctor_get(x_365, 1);
lean_inc(x_369);
lean_dec_ref(x_365);
lean_inc(x_1);
x_370 = l_Lean_MVarId_getType(x_1, x_361, x_360, x_362, x_358, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec_ref(x_370);
x_373 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_358);
lean_inc_ref(x_362);
lean_inc(x_360);
lean_inc_ref(x_361);
x_374 = l_Lean_Meta_mkEqOfHEq(x_373, x_22, x_361, x_360, x_362, x_358, x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec_ref(x_374);
lean_inc(x_360);
x_377 = l_Lean_Meta_mkNoConfusion(x_371, x_375, x_361, x_360, x_362, x_358, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec_ref(x_377);
x_380 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_378, x_360, x_379);
lean_dec(x_360);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_380, 0);
lean_dec(x_382);
x_383 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_2);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_380, 0, x_385);
return x_380;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_386 = lean_ctor_get(x_380, 1);
lean_inc(x_386);
lean_dec(x_380);
x_387 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_2);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_386);
return x_390;
}
}
else
{
uint8_t x_391; 
lean_dec(x_360);
lean_dec(x_1);
x_391 = !lean_is_exclusive(x_377);
if (x_391 == 0)
{
return x_377;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_377, 0);
x_393 = lean_ctor_get(x_377, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_377);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
uint8_t x_395; 
lean_dec(x_371);
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_374);
if (x_395 == 0)
{
return x_374;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_374, 0);
x_397 = lean_ctor_get(x_374, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_374);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_14);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_370);
if (x_399 == 0)
{
return x_370;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_370, 0);
x_401 = lean_ctor_get(x_370, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_370);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
}
else
{
uint8_t x_403; 
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_365);
if (x_403 == 0)
{
return x_365;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_365, 0);
x_405 = lean_ctor_get(x_365, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_365);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
block_452:
{
lean_object* x_414; 
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc_ref(x_17);
x_414 = l_Lean_Meta_matchHEq_x3f(x_17, x_409, x_410, x_411, x_412, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec_ref(x_414);
x_347 = x_408;
x_348 = x_16;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_416;
goto block_356;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
lean_dec_ref(x_415);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
lean_dec_ref(x_414);
x_421 = lean_ctor_get(x_417, 0);
lean_inc(x_421);
lean_dec(x_417);
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
lean_dec(x_418);
x_423 = lean_ctor_get(x_419, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_419, 1);
lean_inc(x_424);
lean_dec(x_419);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
x_425 = l_Lean_Meta_matchConstructorApp_x3f(x_422, x_409, x_410, x_411, x_412, x_420);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_421);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec_ref(x_425);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_427;
goto block_356;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_dec_ref(x_425);
x_429 = lean_ctor_get(x_426, 0);
lean_inc(x_429);
lean_dec_ref(x_426);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
x_430 = l_Lean_Meta_matchConstructorApp_x3f(x_424, x_409, x_410, x_411, x_412, x_428);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
lean_dec(x_429);
lean_dec(x_423);
lean_dec(x_421);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec_ref(x_430);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_432;
goto block_356;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_433 = lean_ctor_get(x_429, 0);
lean_inc_ref(x_433);
lean_dec(x_429);
x_434 = lean_ctor_get(x_431, 0);
lean_inc(x_434);
lean_dec_ref(x_431);
x_435 = lean_ctor_get(x_434, 0);
lean_inc_ref(x_435);
lean_dec(x_434);
x_436 = lean_ctor_get(x_430, 1);
lean_inc(x_436);
lean_dec_ref(x_430);
x_437 = lean_ctor_get(x_433, 0);
lean_inc(x_437);
lean_dec_ref(x_433);
x_438 = lean_ctor_get(x_435, 0);
lean_inc(x_438);
lean_dec_ref(x_435);
x_439 = lean_name_eq(x_437, x_438);
lean_dec(x_438);
lean_dec(x_437);
if (x_439 == 0)
{
x_357 = x_423;
x_358 = x_412;
x_359 = x_408;
x_360 = x_410;
x_361 = x_409;
x_362 = x_411;
x_363 = x_421;
x_364 = x_436;
goto block_407;
}
else
{
if (x_16 == 0)
{
lean_dec(x_423);
lean_dec(x_421);
x_347 = x_408;
x_348 = x_22;
x_349 = x_409;
x_350 = x_410;
x_351 = x_411;
x_352 = x_412;
x_353 = x_436;
goto block_356;
}
else
{
x_357 = x_423;
x_358 = x_412;
x_359 = x_408;
x_360 = x_410;
x_361 = x_409;
x_362 = x_411;
x_363 = x_421;
x_364 = x_436;
goto block_407;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_429);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_430);
if (x_440 == 0)
{
return x_430;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_430, 0);
x_442 = lean_ctor_get(x_430, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_430);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_425);
if (x_444 == 0)
{
return x_425;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_425, 0);
x_446 = lean_ctor_get(x_425, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_425);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_414);
if (x_448 == 0)
{
return x_414;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_414, 0);
x_450 = lean_ctor_get(x_414, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_414);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
block_484:
{
lean_object* x_458; 
lean_inc(x_1);
x_458 = l_Lean_MVarId_getType(x_1, x_456, x_457, x_453, x_455, x_454);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec_ref(x_458);
x_461 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_457);
x_462 = l_Lean_Meta_mkNoConfusion(x_459, x_461, x_456, x_457, x_453, x_455, x_460);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_465 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_463, x_457, x_464);
lean_dec(x_457);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_465, 0);
lean_dec(x_467);
x_468 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_2);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_465, 0, x_470);
return x_465;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_471 = lean_ctor_get(x_465, 1);
lean_inc(x_471);
lean_dec(x_465);
x_472 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_2);
x_474 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_471);
return x_475;
}
}
else
{
uint8_t x_476; 
lean_dec(x_457);
lean_dec(x_1);
x_476 = !lean_is_exclusive(x_462);
if (x_476 == 0)
{
return x_462;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_462, 0);
x_478 = lean_ctor_get(x_462, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_462);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_453);
lean_dec(x_14);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_458);
if (x_480 == 0)
{
return x_458;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_458, 0);
x_482 = lean_ctor_get(x_458, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_458);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
block_525:
{
lean_object* x_490; 
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
lean_inc_ref(x_17);
x_490 = l_Lean_Meta_matchEq_x3f(x_17, x_485, x_486, x_487, x_488, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; 
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
x_408 = x_16;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_492;
goto block_452;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec_ref(x_491);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
lean_dec_ref(x_490);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_494, 1);
lean_inc(x_497);
lean_dec(x_494);
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
x_498 = l_Lean_Meta_matchConstructorApp_x3f(x_496, x_485, x_486, x_487, x_488, x_495);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; 
lean_dec(x_497);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec_ref(x_498);
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_500;
goto block_452;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec_ref(x_498);
x_502 = lean_ctor_get(x_499, 0);
lean_inc(x_502);
lean_dec_ref(x_499);
lean_inc(x_488);
lean_inc_ref(x_487);
lean_inc(x_486);
lean_inc_ref(x_485);
x_503 = l_Lean_Meta_matchConstructorApp_x3f(x_497, x_485, x_486, x_487, x_488, x_501);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
lean_dec(x_502);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec_ref(x_503);
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_505;
goto block_452;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_506 = lean_ctor_get(x_502, 0);
lean_inc_ref(x_506);
lean_dec(x_502);
x_507 = lean_ctor_get(x_504, 0);
lean_inc(x_507);
lean_dec_ref(x_504);
x_508 = lean_ctor_get(x_507, 0);
lean_inc_ref(x_508);
lean_dec(x_507);
x_509 = lean_ctor_get(x_503, 1);
lean_inc(x_509);
lean_dec_ref(x_503);
x_510 = lean_ctor_get(x_506, 0);
lean_inc(x_510);
lean_dec_ref(x_506);
x_511 = lean_ctor_get(x_508, 0);
lean_inc(x_511);
lean_dec_ref(x_508);
x_512 = lean_name_eq(x_510, x_511);
lean_dec(x_511);
lean_dec(x_510);
if (x_512 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_453 = x_487;
x_454 = x_509;
x_455 = x_488;
x_456 = x_485;
x_457 = x_486;
goto block_484;
}
else
{
if (x_16 == 0)
{
x_408 = x_22;
x_409 = x_485;
x_410 = x_486;
x_411 = x_487;
x_412 = x_488;
x_413 = x_509;
goto block_452;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_453 = x_487;
x_454 = x_509;
x_455 = x_488;
x_456 = x_485;
x_457 = x_486;
goto block_484;
}
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_502);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_513 = !lean_is_exclusive(x_503);
if (x_513 == 0)
{
return x_503;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_503, 0);
x_515 = lean_ctor_get(x_503, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_503);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_497);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_498);
if (x_517 == 0)
{
return x_498;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_498, 0);
x_519 = lean_ctor_get(x_498, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_498);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_521 = !lean_is_exclusive(x_490);
if (x_521 == 0)
{
return x_490;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_490, 0);
x_523 = lean_ctor_get(x_490, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_490);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
block_666:
{
lean_object* x_531; 
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc_ref(x_17);
x_531 = l_Lean_Meta_matchNe_x3f(x_17, x_526, x_527, x_528, x_529, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec_ref(x_531);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_533;
goto block_525;
}
else
{
uint8_t x_534; 
x_534 = !lean_is_exclusive(x_532);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_535 = lean_ctor_get(x_532, 0);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_ctor_get(x_531, 1);
lean_inc(x_537);
lean_dec_ref(x_531);
x_538 = !lean_is_exclusive(x_536);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_536, 0);
x_540 = lean_ctor_get(x_536, 1);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_539);
x_541 = l_Lean_Meta_isExprDefEq(x_539, x_540, x_526, x_527, x_528, x_529, x_537);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec_ref(x_541);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_544;
goto block_525;
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_545 = lean_ctor_get(x_541, 1);
lean_inc(x_545);
lean_dec_ref(x_541);
lean_inc(x_1);
x_546 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_549 = l_Lean_Meta_mkEqRefl(x_539, x_526, x_527, x_528, x_529, x_548);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec_ref(x_549);
x_552 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_553 = l_Lean_Meta_mkAbsurd(x_547, x_550, x_552, x_526, x_527, x_528, x_529, x_551);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec_ref(x_553);
x_556 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_554, x_527, x_555);
lean_dec(x_527);
x_557 = !lean_is_exclusive(x_556);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_556, 0);
lean_dec(x_558);
x_559 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_536, 1, x_2);
lean_ctor_set(x_536, 0, x_559);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_536);
lean_ctor_set(x_556, 0, x_532);
return x_556;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
lean_dec(x_556);
x_561 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_536, 1, x_2);
lean_ctor_set(x_536, 0, x_561);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_536);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_532);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
}
else
{
uint8_t x_563; 
lean_free_object(x_536);
lean_free_object(x_532);
lean_dec(x_527);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_553);
if (x_563 == 0)
{
return x_553;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_553, 0);
x_565 = lean_ctor_get(x_553, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_553);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_547);
lean_free_object(x_536);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_567 = !lean_is_exclusive(x_549);
if (x_567 == 0)
{
return x_549;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = lean_ctor_get(x_549, 0);
x_569 = lean_ctor_get(x_549, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_549);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
}
else
{
uint8_t x_571; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_571 = !lean_is_exclusive(x_546);
if (x_571 == 0)
{
return x_546;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_546, 0);
x_573 = lean_ctor_get(x_546, 1);
lean_inc(x_573);
lean_inc(x_572);
lean_dec(x_546);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
return x_574;
}
}
}
}
else
{
uint8_t x_575; 
lean_free_object(x_536);
lean_dec(x_539);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_575 = !lean_is_exclusive(x_541);
if (x_575 == 0)
{
return x_541;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_541, 0);
x_577 = lean_ctor_get(x_541, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_541);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_536, 0);
x_580 = lean_ctor_get(x_536, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_536);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_579);
x_581 = l_Lean_Meta_isExprDefEq(x_579, x_580, x_526, x_527, x_528, x_529, x_537);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; uint8_t x_583; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_unbox(x_582);
lean_dec(x_582);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_579);
lean_free_object(x_532);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec_ref(x_581);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_584;
goto block_525;
}
else
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_585 = lean_ctor_get(x_581, 1);
lean_inc(x_585);
lean_dec_ref(x_581);
lean_inc(x_1);
x_586 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec_ref(x_586);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_589 = l_Lean_Meta_mkEqRefl(x_579, x_526, x_527, x_528, x_529, x_588);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec_ref(x_589);
x_592 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_593 = l_Lean_Meta_mkAbsurd(x_587, x_590, x_592, x_526, x_527, x_528, x_529, x_591);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec_ref(x_593);
x_596 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_594, x_527, x_595);
lean_dec(x_527);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
x_599 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_2);
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 0, x_600);
if (lean_is_scalar(x_598)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_598;
}
lean_ctor_set(x_601, 0, x_532);
lean_ctor_set(x_601, 1, x_597);
return x_601;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_free_object(x_532);
lean_dec(x_527);
lean_dec(x_1);
x_602 = lean_ctor_get(x_593, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_593, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_604 = x_593;
} else {
 lean_dec_ref(x_593);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_603);
return x_605;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_587);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_606 = lean_ctor_get(x_589, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_589, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_608 = x_589;
} else {
 lean_dec_ref(x_589);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_579);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_610 = lean_ctor_get(x_586, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_586, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_612 = x_586;
} else {
 lean_dec_ref(x_586);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_579);
lean_free_object(x_532);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_614 = lean_ctor_get(x_581, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_581, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_616 = x_581;
} else {
 lean_dec_ref(x_581);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_618 = lean_ctor_get(x_532, 0);
lean_inc(x_618);
lean_dec(x_532);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
x_620 = lean_ctor_get(x_531, 1);
lean_inc(x_620);
lean_dec_ref(x_531);
x_621 = lean_ctor_get(x_619, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_623 = x_619;
} else {
 lean_dec_ref(x_619);
 x_623 = lean_box(0);
}
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_621);
x_624 = l_Lean_Meta_isExprDefEq(x_621, x_622, x_526, x_527, x_528, x_529, x_620);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; 
lean_dec(x_623);
lean_dec(x_621);
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
lean_dec_ref(x_624);
x_485 = x_526;
x_486 = x_527;
x_487 = x_528;
x_488 = x_529;
x_489 = x_627;
goto block_525;
}
else
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_628 = lean_ctor_get(x_624, 1);
lean_inc(x_628);
lean_dec_ref(x_624);
lean_inc(x_1);
x_629 = l_Lean_MVarId_getType(x_1, x_526, x_527, x_528, x_529, x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec_ref(x_629);
lean_inc(x_529);
lean_inc_ref(x_528);
lean_inc(x_527);
lean_inc_ref(x_526);
x_632 = l_Lean_Meta_mkEqRefl(x_621, x_526, x_527, x_528, x_529, x_631);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec_ref(x_632);
x_635 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_527);
x_636 = l_Lean_Meta_mkAbsurd(x_630, x_633, x_635, x_526, x_527, x_528, x_529, x_634);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec_ref(x_636);
x_639 = l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_637, x_527, x_638);
lean_dec(x_527);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_641 = x_639;
} else {
 lean_dec_ref(x_639);
 x_641 = lean_box(0);
}
x_642 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_623)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_623;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_2);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
if (lean_is_scalar(x_641)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_641;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_640);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_623);
lean_dec(x_527);
lean_dec(x_1);
x_646 = lean_ctor_get(x_636, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_636, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_648 = x_636;
} else {
 lean_dec_ref(x_636);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_630);
lean_dec(x_623);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_650 = lean_ctor_get(x_632, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_632, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_652 = x_632;
} else {
 lean_dec_ref(x_632);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_14);
lean_dec(x_1);
x_654 = lean_ctor_get(x_629, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_629, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_656 = x_629;
} else {
 lean_dec_ref(x_629);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_654);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_658 = lean_ctor_get(x_624, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_624, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_660 = x_624;
} else {
 lean_dec_ref(x_624);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_531);
if (x_662 == 0)
{
return x_531;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_531, 0);
x_664 = lean_ctor_get(x_531, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_531);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
}
else
{
uint8_t x_729; 
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_729 = !lean_is_exclusive(x_18);
if (x_729 == 0)
{
return x_18;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_18, 0);
x_731 = lean_ctor_get(x_18, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_18);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
else
{
lean_object* x_733; lean_object* x_734; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_15)) {
 x_733 = lean_alloc_ctor(1, 1, 0);
} else {
 x_733 = x_15;
}
lean_ctor_set(x_733, 0, x_4);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_11);
return x_734;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_6, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec_ref(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
x_24 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0___lam__0), 11, 4);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_array_size(x_13);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3(x_24, x_25, x_13, x_27, x_28, x_26, x_7, x_8, x_9, x_10, x_22);
lean_dec_ref(x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec_ref(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec_ref(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
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
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0;
x_19 = l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0(x_3, x_1, x_18, x_17, x_16, x_18, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec_ref(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec_ref(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
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
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_contradictionCore___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_contradictionCore___closed__0;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_contradictionCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Lean_MVarId_contradictionCore___closed__0;
x_13 = lean_box(0);
x_14 = l_Lean_Meta_throwTacticEx___redArg(x_12, x_1, x_13, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Contradiction", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4437u);
x_2 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
x_3 = 0;
x_4 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0 = _init_l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__0);
l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1 = _init_l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_MVarId_assign___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1);
l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1);
l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6);
l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7);
l_Lean_Meta_ElimEmptyInductive_elim___closed__0 = _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__0();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___closed__0);
l_Lean_Meta_ElimEmptyInductive_elim___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___closed__2);
l_Lean_Meta_mkGenDiseqMask___closed__0 = _init_l_Lean_Meta_mkGenDiseqMask___closed__0();
lean_mark_persistent(l_Lean_Meta_mkGenDiseqMask___closed__0);
l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0);
l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0 = _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0();
lean_mark_persistent(l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__0);
l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1 = _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1();
lean_mark_persistent(l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__1);
l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2 = _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2();
lean_mark_persistent(l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__2);
l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3 = _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3();
lean_mark_persistent(l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__3);
l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4 = _init_l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4();
lean_mark_persistent(l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4_spec__4___closed__4);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__0);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__1);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__2);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__3);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__4);
l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5 = _init_l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__4___closed__5);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1();
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8);
l_Lean_MVarId_contradictionCore___closed__0 = _init_l_Lean_MVarId_contradictionCore___closed__0();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___closed__0);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
