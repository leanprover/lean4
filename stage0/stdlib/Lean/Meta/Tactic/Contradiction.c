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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__2;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM;
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__2;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__5;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__1;
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__6;
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_contradictionCore___closed__0;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__5;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
uint8_t l_Lean_Expr_isHEq(lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__0;
static lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg___closed__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_ElimEmptyInductive_elim_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_ElimEmptyInductive_elim_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGenDiseqMask___closed__0;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_object* l_panic___at___Lean_Meta_ACLt_main_lexSameCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_23 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_21, x_3, x_22);
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
x_55 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_53, x_3, x_54);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_saveState___boxed), 5, 0);
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
x_2 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0;
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
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
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
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
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
x_29 = l_Lean_commitWhen___at___Lean_Meta_ElimEmptyInductive_elim_spec__6(x_28, x_3, x_4, x_5, x_6, x_7, x_25);
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
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_106 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_108 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_128 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_61 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_64 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_220 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_179 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0;
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
x_23 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_20, x_14, x_21, x_22, x_11, x_5, x_6, x_7, x_8, x_12);
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
x_29 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_28, x_6, x_26);
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
x_32 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_30, x_5, x_6, x_7, x_8, x_31);
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
x_84 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_80, x_75, x_82, x_83, x_81, x_5, x_6, x_7, x_8, x_12);
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
x_90 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_89, x_6, x_87);
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
x_93 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_91, x_5, x_6, x_7, x_8, x_92);
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
x_3 = lean_unsigned_to_nat(115u);
x_4 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_38; 
x_38 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_38);
x_8 = x_38;
goto block_37;
block_37:
{
uint8_t x_9; 
lean_inc_ref(x_8);
x_9 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
x_11 = l_panic___at___Lean_Meta_ACLt_main_lexSameCtor_spec__0(x_10, x_3, x_4, x_5, x_6, x_7);
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
x_16 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_14, x_15, x_3, x_4, x_5, x_6, x_7);
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
x_26 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_25, x_4, x_24);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_13;
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
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
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; uint8_t x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_682; lean_object* x_754; 
x_17 = 1;
x_754 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_754);
x_682 = x_754;
goto block_753;
block_48:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec_ref(x_3);
x_25 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_1, x_23, x_24, x_22, x_20, x_19, x_18, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
if (lean_is_scalar(x_15)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_15;
}
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
if (lean_is_scalar(x_15)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_15;
}
lean_ctor_set(x_32, 0, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_4);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_15;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_15;
 lean_ctor_set_tag(x_42, 0);
}
lean_ctor_set(x_42, 0, x_41);
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
lean_dec(x_15);
lean_dec_ref(x_4);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
block_55:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_18 = x_49;
x_19 = x_50;
x_20 = x_51;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
goto block_48;
}
block_64:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_60);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
x_49 = x_56;
x_50 = x_57;
x_51 = x_58;
x_52 = x_59;
x_53 = x_60;
goto block_55;
}
}
block_71:
{
if (x_65 == 0)
{
x_49 = x_66;
x_50 = x_67;
x_51 = x_68;
x_52 = x_69;
x_53 = x_70;
goto block_55;
}
else
{
x_56 = x_66;
x_57 = x_67;
x_58 = x_68;
x_59 = x_69;
x_60 = x_70;
x_61 = x_16;
goto block_64;
}
}
block_79:
{
if (x_78 == 0)
{
x_56 = x_73;
x_57 = x_74;
x_58 = x_75;
x_59 = x_76;
x_60 = x_77;
x_61 = x_16;
goto block_64;
}
else
{
x_65 = x_72;
x_66 = x_73;
x_67 = x_74;
x_68 = x_75;
x_69 = x_76;
x_70 = x_77;
goto block_71;
}
}
block_88:
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_87 == 0)
{
x_72 = x_80;
x_73 = x_85;
x_74 = x_84;
x_75 = x_83;
x_76 = x_86;
x_77 = x_82;
x_78 = x_16;
goto block_79;
}
else
{
if (x_81 == 0)
{
x_65 = x_80;
x_66 = x_85;
x_67 = x_84;
x_68 = x_83;
x_69 = x_86;
x_70 = x_82;
goto block_71;
}
else
{
x_72 = x_80;
x_73 = x_85;
x_74 = x_84;
x_75 = x_83;
x_76 = x_86;
x_77 = x_82;
x_78 = x_16;
goto block_79;
}
}
}
block_115:
{
if (x_96 == 0)
{
x_80 = x_91;
x_81 = x_93;
x_82 = x_90;
x_83 = x_94;
x_84 = x_95;
x_85 = x_92;
x_86 = x_89;
goto block_88;
}
else
{
lean_object* x_97; 
lean_inc(x_92);
lean_inc_ref(x_95);
lean_inc(x_94);
lean_inc_ref(x_90);
lean_inc(x_14);
lean_inc(x_1);
x_97 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_1, x_14, x_90, x_94, x_95, x_92, x_89);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec_ref(x_97);
x_80 = x_91;
x_81 = x_93;
x_82 = x_90;
x_83 = x_94;
x_84 = x_95;
x_85 = x_92;
x_86 = x_100;
goto block_88;
}
else
{
uint8_t x_101; 
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec_ref(x_90);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_dec(x_102);
x_103 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_2);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_97, 0, x_105);
return x_97;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_dec(x_97);
x_107 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_2);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec_ref(x_90);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_97);
if (x_111 == 0)
{
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
block_126:
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
if (x_124 == 0)
{
lean_dec_ref(x_118);
x_89 = x_123;
x_90 = x_119;
x_91 = x_116;
x_92 = x_122;
x_93 = x_117;
x_94 = x_120;
x_95 = x_121;
x_96 = x_16;
goto block_115;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_118);
x_89 = x_123;
x_90 = x_119;
x_91 = x_116;
x_92 = x_122;
x_93 = x_117;
x_94 = x_120;
x_95 = x_121;
x_96 = x_125;
goto block_115;
}
}
block_138:
{
if (x_136 == 0)
{
lean_dec_ref(x_131);
x_116 = x_127;
x_117 = x_128;
x_118 = x_134;
x_119 = x_129;
x_120 = x_133;
x_121 = x_132;
x_122 = x_135;
x_123 = x_130;
goto block_126;
}
else
{
lean_object* x_137; 
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_129);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
}
block_150:
{
uint8_t x_148; 
x_148 = l_Lean_Exception_isInterrupt(x_146);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Exception_isRuntime(x_146);
x_127 = x_139;
x_128 = x_140;
x_129 = x_141;
x_130 = x_147;
x_131 = x_146;
x_132 = x_143;
x_133 = x_142;
x_134 = x_144;
x_135 = x_145;
x_136 = x_149;
goto block_138;
}
else
{
x_127 = x_139;
x_128 = x_140;
x_129 = x_141;
x_130 = x_147;
x_131 = x_146;
x_132 = x_143;
x_133 = x_142;
x_134 = x_144;
x_135 = x_145;
x_136 = x_148;
goto block_138;
}
}
block_312:
{
lean_object* x_159; 
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc_ref(x_153);
lean_inc_ref(x_156);
x_159 = l_Lean_Meta_mkDecide(x_156, x_153, x_155, x_154, x_158, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = l_Lean_Meta_Context_config(x_153);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_164 = lean_ctor_get_uint8(x_153, sizeof(void*)*7);
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_153, 2);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_153, 3);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_153, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_153, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_153, 6);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_153, sizeof(void*)*7 + 1);
x_172 = lean_ctor_get_uint8(x_153, sizeof(void*)*7 + 2);
x_173 = 1;
lean_ctor_set_uint8(x_162, 9, x_173);
x_174 = l_Lean_Meta_Context_configKey(x_153);
x_175 = 2;
x_176 = lean_uint64_shift_right(x_174, x_175);
x_177 = lean_uint64_shift_left(x_176, x_175);
x_178 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_179 = lean_uint64_lor(x_177, x_178);
x_180 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set_uint64(x_180, sizeof(void*)*1, x_179);
x_181 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_165);
lean_ctor_set(x_181, 2, x_166);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_168);
lean_ctor_set(x_181, 5, x_169);
lean_ctor_set(x_181, 6, x_170);
lean_ctor_set_uint8(x_181, sizeof(void*)*7, x_164);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 1, x_171);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 2, x_172);
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc(x_160);
x_182 = lean_whnf(x_160, x_181, x_155, x_154, x_158, x_161);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
x_185 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_186 = l_Lean_Expr_isConstOf(x_183, x_185);
lean_dec(x_183);
if (x_186 == 0)
{
lean_dec(x_160);
x_116 = x_151;
x_117 = x_152;
x_118 = x_156;
x_119 = x_153;
x_120 = x_155;
x_121 = x_154;
x_122 = x_158;
x_123 = x_184;
goto block_126;
}
else
{
lean_object* x_187; 
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc_ref(x_153);
lean_inc(x_160);
x_187 = l_Lean_Meta_mkEqRefl(x_160, x_153, x_155, x_154, x_158, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
lean_inc(x_1);
x_190 = l_Lean_MVarId_getType(x_1, x_153, x_155, x_154, x_158, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
x_193 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_194 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_195 = l_Lean_Expr_getAppNumArgs(x_160);
lean_inc(x_195);
x_196 = lean_mk_array(x_195, x_194);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_sub(x_195, x_197);
lean_dec(x_195);
x_199 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_160, x_196, x_198);
x_200 = lean_array_push(x_199, x_188);
x_201 = l_Lean_mkAppN(x_193, x_200);
lean_dec_ref(x_200);
lean_inc(x_14);
x_202 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc_ref(x_153);
x_203 = l_Lean_Meta_mkAbsurd(x_191, x_202, x_201, x_153, x_155, x_154, x_158, x_192);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
lean_dec(x_158);
lean_dec_ref(x_156);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_205, x_155, x_206);
lean_dec(x_155);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
x_210 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 0, x_210);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_203);
lean_ctor_set(x_207, 0, x_211);
return x_207;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 0, x_213);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_203);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_203, 0);
x_217 = lean_ctor_get(x_203, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_203);
x_218 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_216, x_155, x_217);
lean_dec(x_155);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
x_221 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_2);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_220)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_220;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_219);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_203, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_203, 1);
lean_inc(x_226);
lean_dec_ref(x_203);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_225;
x_147 = x_226;
goto block_150;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_188);
lean_dec(x_160);
x_227 = lean_ctor_get(x_190, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_190, 1);
lean_inc(x_228);
lean_dec_ref(x_190);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_227;
x_147 = x_228;
goto block_150;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_160);
x_229 = lean_ctor_get(x_187, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_187, 1);
lean_inc(x_230);
lean_dec_ref(x_187);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_229;
x_147 = x_230;
goto block_150;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_160);
x_231 = lean_ctor_get(x_182, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_182, 1);
lean_inc(x_232);
lean_dec_ref(x_182);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_231;
x_147 = x_232;
goto block_150;
}
}
else
{
uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_233 = lean_ctor_get_uint8(x_162, 0);
x_234 = lean_ctor_get_uint8(x_162, 1);
x_235 = lean_ctor_get_uint8(x_162, 2);
x_236 = lean_ctor_get_uint8(x_162, 3);
x_237 = lean_ctor_get_uint8(x_162, 4);
x_238 = lean_ctor_get_uint8(x_162, 5);
x_239 = lean_ctor_get_uint8(x_162, 6);
x_240 = lean_ctor_get_uint8(x_162, 7);
x_241 = lean_ctor_get_uint8(x_162, 8);
x_242 = lean_ctor_get_uint8(x_162, 10);
x_243 = lean_ctor_get_uint8(x_162, 11);
x_244 = lean_ctor_get_uint8(x_162, 12);
x_245 = lean_ctor_get_uint8(x_162, 13);
x_246 = lean_ctor_get_uint8(x_162, 14);
x_247 = lean_ctor_get_uint8(x_162, 15);
x_248 = lean_ctor_get_uint8(x_162, 16);
x_249 = lean_ctor_get_uint8(x_162, 17);
x_250 = lean_ctor_get_uint8(x_162, 18);
lean_dec(x_162);
x_251 = lean_ctor_get_uint8(x_153, sizeof(void*)*7);
x_252 = lean_ctor_get(x_153, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_153, 2);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_153, 3);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_153, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_153, 5);
lean_inc(x_256);
x_257 = lean_ctor_get(x_153, 6);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_153, sizeof(void*)*7 + 1);
x_259 = lean_ctor_get_uint8(x_153, sizeof(void*)*7 + 2);
x_260 = 1;
x_261 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_261, 0, x_233);
lean_ctor_set_uint8(x_261, 1, x_234);
lean_ctor_set_uint8(x_261, 2, x_235);
lean_ctor_set_uint8(x_261, 3, x_236);
lean_ctor_set_uint8(x_261, 4, x_237);
lean_ctor_set_uint8(x_261, 5, x_238);
lean_ctor_set_uint8(x_261, 6, x_239);
lean_ctor_set_uint8(x_261, 7, x_240);
lean_ctor_set_uint8(x_261, 8, x_241);
lean_ctor_set_uint8(x_261, 9, x_260);
lean_ctor_set_uint8(x_261, 10, x_242);
lean_ctor_set_uint8(x_261, 11, x_243);
lean_ctor_set_uint8(x_261, 12, x_244);
lean_ctor_set_uint8(x_261, 13, x_245);
lean_ctor_set_uint8(x_261, 14, x_246);
lean_ctor_set_uint8(x_261, 15, x_247);
lean_ctor_set_uint8(x_261, 16, x_248);
lean_ctor_set_uint8(x_261, 17, x_249);
lean_ctor_set_uint8(x_261, 18, x_250);
x_262 = l_Lean_Meta_Context_configKey(x_153);
x_263 = 2;
x_264 = lean_uint64_shift_right(x_262, x_263);
x_265 = lean_uint64_shift_left(x_264, x_263);
x_266 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_267 = lean_uint64_lor(x_265, x_266);
x_268 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_268, 0, x_261);
lean_ctor_set_uint64(x_268, sizeof(void*)*1, x_267);
x_269 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_252);
lean_ctor_set(x_269, 2, x_253);
lean_ctor_set(x_269, 3, x_254);
lean_ctor_set(x_269, 4, x_255);
lean_ctor_set(x_269, 5, x_256);
lean_ctor_set(x_269, 6, x_257);
lean_ctor_set_uint8(x_269, sizeof(void*)*7, x_251);
lean_ctor_set_uint8(x_269, sizeof(void*)*7 + 1, x_258);
lean_ctor_set_uint8(x_269, sizeof(void*)*7 + 2, x_259);
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc(x_160);
x_270 = lean_whnf(x_160, x_269, x_155, x_154, x_158, x_161);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_274 = l_Lean_Expr_isConstOf(x_271, x_273);
lean_dec(x_271);
if (x_274 == 0)
{
lean_dec(x_160);
x_116 = x_151;
x_117 = x_152;
x_118 = x_156;
x_119 = x_153;
x_120 = x_155;
x_121 = x_154;
x_122 = x_158;
x_123 = x_272;
goto block_126;
}
else
{
lean_object* x_275; 
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc_ref(x_153);
lean_inc(x_160);
x_275 = l_Lean_Meta_mkEqRefl(x_160, x_153, x_155, x_154, x_158, x_272);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
lean_inc(x_1);
x_278 = l_Lean_MVarId_getType(x_1, x_153, x_155, x_154, x_158, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec_ref(x_278);
x_281 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_282 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_283 = l_Lean_Expr_getAppNumArgs(x_160);
lean_inc(x_283);
x_284 = lean_mk_array(x_283, x_282);
x_285 = lean_unsigned_to_nat(1u);
x_286 = lean_nat_sub(x_283, x_285);
lean_dec(x_283);
x_287 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_160, x_284, x_286);
x_288 = lean_array_push(x_287, x_276);
x_289 = l_Lean_mkAppN(x_281, x_288);
lean_dec_ref(x_288);
lean_inc(x_14);
x_290 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_158);
lean_inc_ref(x_154);
lean_inc(x_155);
lean_inc_ref(x_153);
x_291 = l_Lean_Meta_mkAbsurd(x_279, x_290, x_289, x_153, x_155, x_154, x_158, x_280);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_158);
lean_dec_ref(x_156);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
x_295 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_292, x_155, x_293);
lean_dec(x_155);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_294)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_294;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_2);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_299);
if (lean_is_scalar(x_297)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_297;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_296);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_291, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_291, 1);
lean_inc(x_303);
lean_dec_ref(x_291);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_302;
x_147 = x_303;
goto block_150;
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_276);
lean_dec(x_160);
x_304 = lean_ctor_get(x_278, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_278, 1);
lean_inc(x_305);
lean_dec_ref(x_278);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_304;
x_147 = x_305;
goto block_150;
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_160);
x_306 = lean_ctor_get(x_275, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_275, 1);
lean_inc(x_307);
lean_dec_ref(x_275);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_306;
x_147 = x_307;
goto block_150;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_160);
x_308 = lean_ctor_get(x_270, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_270, 1);
lean_inc(x_309);
lean_dec_ref(x_270);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_308;
x_147 = x_309;
goto block_150;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_159, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_159, 1);
lean_inc(x_311);
lean_dec_ref(x_159);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_155;
x_143 = x_154;
x_144 = x_156;
x_145 = x_158;
x_146 = x_310;
x_147 = x_311;
goto block_150;
}
}
block_322:
{
if (x_321 == 0)
{
x_116 = x_313;
x_117 = x_314;
x_118 = x_318;
x_119 = x_315;
x_120 = x_317;
x_121 = x_316;
x_122 = x_320;
x_123 = x_319;
goto block_126;
}
else
{
x_151 = x_313;
x_152 = x_314;
x_153 = x_315;
x_154 = x_316;
x_155 = x_317;
x_156 = x_318;
x_157 = x_319;
x_158 = x_320;
goto block_312;
}
}
block_333:
{
uint8_t x_332; 
x_332 = l_Lean_Expr_hasFVar(x_326);
lean_dec_ref(x_326);
if (x_332 == 0)
{
x_151 = x_323;
x_152 = x_324;
x_153 = x_325;
x_154 = x_328;
x_155 = x_327;
x_156 = x_329;
x_157 = x_330;
x_158 = x_331;
goto block_312;
}
else
{
x_313 = x_323;
x_314 = x_324;
x_315 = x_325;
x_316 = x_328;
x_317 = x_327;
x_318 = x_329;
x_319 = x_330;
x_320 = x_331;
x_321 = x_16;
goto block_322;
}
}
block_346:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_inc_ref(x_339);
x_342 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_339, x_338, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = l_Lean_Expr_hasMVar(x_343);
if (x_345 == 0)
{
x_323 = x_334;
x_324 = x_335;
x_325 = x_336;
x_326 = x_343;
x_327 = x_338;
x_328 = x_337;
x_329 = x_339;
x_330 = x_344;
x_331 = x_341;
goto block_333;
}
else
{
if (x_16 == 0)
{
lean_dec(x_343);
x_313 = x_334;
x_314 = x_335;
x_315 = x_336;
x_316 = x_337;
x_317 = x_338;
x_318 = x_339;
x_319 = x_344;
x_320 = x_341;
x_321 = x_16;
goto block_322;
}
else
{
x_323 = x_334;
x_324 = x_335;
x_325 = x_336;
x_326 = x_343;
x_327 = x_338;
x_328 = x_337;
x_329 = x_339;
x_330 = x_344;
x_331 = x_341;
goto block_333;
}
}
}
block_356:
{
if (x_355 == 0)
{
x_116 = x_347;
x_117 = x_348;
x_118 = x_352;
x_119 = x_349;
x_120 = x_351;
x_121 = x_350;
x_122 = x_354;
x_123 = x_353;
goto block_126;
}
else
{
x_334 = x_347;
x_335 = x_348;
x_336 = x_349;
x_337 = x_350;
x_338 = x_351;
x_339 = x_352;
x_340 = x_353;
x_341 = x_354;
goto block_346;
}
}
block_367:
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_365 == 0)
{
x_347 = x_359;
x_348 = x_357;
x_349 = x_360;
x_350 = x_362;
x_351 = x_361;
x_352 = x_358;
x_353 = x_364;
x_354 = x_363;
x_355 = x_16;
goto block_356;
}
else
{
uint8_t x_366; 
x_366 = l_Lean_Expr_hasFVar(x_358);
if (x_366 == 0)
{
x_334 = x_359;
x_335 = x_357;
x_336 = x_360;
x_337 = x_362;
x_338 = x_361;
x_339 = x_358;
x_340 = x_364;
x_341 = x_363;
goto block_346;
}
else
{
x_347 = x_359;
x_348 = x_357;
x_349 = x_360;
x_350 = x_362;
x_351 = x_361;
x_352 = x_358;
x_353 = x_364;
x_354 = x_363;
x_355 = x_16;
goto block_356;
}
}
}
block_419:
{
lean_object* x_377; 
lean_inc(x_376);
lean_inc_ref(x_372);
lean_inc(x_369);
lean_inc_ref(x_370);
x_377 = l_Lean_Meta_isExprDefEq(x_374, x_375, x_370, x_369, x_372, x_376, x_371);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_unbox(x_378);
lean_dec(x_378);
if (x_379 == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec_ref(x_377);
x_357 = x_368;
x_358 = x_373;
x_359 = x_17;
x_360 = x_370;
x_361 = x_369;
x_362 = x_372;
x_363 = x_376;
x_364 = x_380;
goto block_367;
}
else
{
lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_373);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_381 = lean_ctor_get(x_377, 1);
lean_inc(x_381);
lean_dec_ref(x_377);
lean_inc(x_1);
x_382 = l_Lean_MVarId_getType(x_1, x_370, x_369, x_372, x_376, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec_ref(x_382);
x_385 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_376);
lean_inc_ref(x_372);
lean_inc(x_369);
lean_inc_ref(x_370);
x_386 = l_Lean_Meta_mkEqOfHEq(x_385, x_17, x_370, x_369, x_372, x_376, x_384);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec_ref(x_386);
lean_inc(x_369);
x_389 = l_Lean_Meta_mkNoConfusion(x_383, x_387, x_370, x_369, x_372, x_376, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec_ref(x_389);
x_392 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_390, x_369, x_391);
lean_dec(x_369);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_392, 0);
lean_dec(x_394);
x_395 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_2);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_392, 0, x_397);
return x_392;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_398 = lean_ctor_get(x_392, 1);
lean_inc(x_398);
lean_dec(x_392);
x_399 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_2);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_398);
return x_402;
}
}
else
{
uint8_t x_403; 
lean_dec(x_369);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_389);
if (x_403 == 0)
{
return x_389;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_389, 0);
x_405 = lean_ctor_get(x_389, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_389);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_383);
lean_dec(x_376);
lean_dec_ref(x_372);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_386);
if (x_407 == 0)
{
return x_386;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_386, 0);
x_409 = lean_ctor_get(x_386, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_386);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_376);
lean_dec_ref(x_372);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_14);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_382);
if (x_411 == 0)
{
return x_382;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_382, 0);
x_413 = lean_ctor_get(x_382, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_382);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_376);
lean_dec_ref(x_373);
lean_dec_ref(x_372);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_377);
if (x_415 == 0)
{
return x_377;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_377, 0);
x_417 = lean_ctor_get(x_377, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_377);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
block_465:
{
lean_object* x_427; 
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
lean_inc_ref(x_420);
x_427 = l_Lean_Meta_matchHEq_x3f(x_420, x_422, x_423, x_424, x_425, x_426);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec_ref(x_427);
x_357 = x_421;
x_358 = x_420;
x_359 = x_16;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_429;
goto block_367;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
lean_dec_ref(x_428);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_427, 1);
lean_inc(x_433);
lean_dec_ref(x_427);
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
lean_dec(x_430);
x_435 = lean_ctor_get(x_431, 0);
lean_inc(x_435);
lean_dec(x_431);
x_436 = lean_ctor_get(x_432, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_432, 1);
lean_inc(x_437);
lean_dec(x_432);
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
x_438 = l_Lean_Meta_matchConstructorApp_x3f(x_435, x_422, x_423, x_424, x_425, x_433);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec_ref(x_438);
x_357 = x_421;
x_358 = x_420;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_440;
goto block_367;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec_ref(x_438);
x_442 = lean_ctor_get(x_439, 0);
lean_inc(x_442);
lean_dec_ref(x_439);
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
x_443 = l_Lean_Meta_matchConstructorApp_x3f(x_437, x_422, x_423, x_424, x_425, x_441);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
lean_dec(x_442);
lean_dec(x_436);
lean_dec(x_434);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec_ref(x_443);
x_357 = x_421;
x_358 = x_420;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_445;
goto block_367;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_446 = lean_ctor_get(x_442, 0);
lean_inc_ref(x_446);
lean_dec(x_442);
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
lean_dec_ref(x_444);
x_448 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_448);
lean_dec(x_447);
x_449 = lean_ctor_get(x_443, 1);
lean_inc(x_449);
lean_dec_ref(x_443);
x_450 = lean_ctor_get(x_446, 0);
lean_inc(x_450);
lean_dec_ref(x_446);
x_451 = lean_ctor_get(x_448, 0);
lean_inc(x_451);
lean_dec_ref(x_448);
x_452 = lean_name_eq(x_450, x_451);
lean_dec(x_451);
lean_dec(x_450);
if (x_452 == 0)
{
x_368 = x_421;
x_369 = x_423;
x_370 = x_422;
x_371 = x_449;
x_372 = x_424;
x_373 = x_420;
x_374 = x_434;
x_375 = x_436;
x_376 = x_425;
goto block_419;
}
else
{
if (x_16 == 0)
{
lean_dec(x_436);
lean_dec(x_434);
x_357 = x_421;
x_358 = x_420;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_449;
goto block_367;
}
else
{
x_368 = x_421;
x_369 = x_423;
x_370 = x_422;
x_371 = x_449;
x_372 = x_424;
x_373 = x_420;
x_374 = x_434;
x_375 = x_436;
x_376 = x_425;
goto block_419;
}
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_442);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_443);
if (x_453 == 0)
{
return x_443;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_443, 0);
x_455 = lean_ctor_get(x_443, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_443);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_457 = !lean_is_exclusive(x_438);
if (x_457 == 0)
{
return x_438;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_438, 0);
x_459 = lean_ctor_get(x_438, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_438);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_427);
if (x_461 == 0)
{
return x_427;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_427, 0);
x_463 = lean_ctor_get(x_427, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_427);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
block_497:
{
lean_object* x_471; 
lean_inc(x_1);
x_471 = l_Lean_MVarId_getType(x_1, x_469, x_466, x_467, x_468, x_470);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec_ref(x_471);
x_474 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_466);
x_475 = l_Lean_Meta_mkNoConfusion(x_472, x_474, x_469, x_466, x_467, x_468, x_473);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec_ref(x_475);
x_478 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_476, x_466, x_477);
lean_dec(x_466);
x_479 = !lean_is_exclusive(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_480 = lean_ctor_get(x_478, 0);
lean_dec(x_480);
x_481 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_2);
x_483 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_478, 0, x_483);
return x_478;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_478, 1);
lean_inc(x_484);
lean_dec(x_478);
x_485 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_2);
x_487 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_484);
return x_488;
}
}
else
{
uint8_t x_489; 
lean_dec(x_466);
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_475);
if (x_489 == 0)
{
return x_475;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_475, 0);
x_491 = lean_ctor_get(x_475, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_475);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
uint8_t x_493; 
lean_dec_ref(x_469);
lean_dec(x_468);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_14);
lean_dec(x_1);
x_493 = !lean_is_exclusive(x_471);
if (x_493 == 0)
{
return x_471;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_471, 0);
x_495 = lean_ctor_get(x_471, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_471);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
block_539:
{
lean_object* x_504; 
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
lean_inc_ref(x_498);
x_504 = l_Lean_Meta_matchEq_x3f(x_498, x_499, x_500, x_501, x_502, x_503);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec_ref(x_504);
x_420 = x_498;
x_421 = x_16;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_506;
goto block_465;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
lean_dec_ref(x_505);
x_508 = lean_ctor_get(x_507, 1);
lean_inc(x_508);
lean_dec(x_507);
x_509 = lean_ctor_get(x_504, 1);
lean_inc(x_509);
lean_dec_ref(x_504);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
lean_dec(x_508);
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
x_512 = l_Lean_Meta_matchConstructorApp_x3f(x_510, x_499, x_500, x_501, x_502, x_509);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; 
lean_dec(x_511);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec_ref(x_512);
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_514;
goto block_465;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_515);
lean_dec_ref(x_512);
x_516 = lean_ctor_get(x_513, 0);
lean_inc(x_516);
lean_dec_ref(x_513);
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
x_517 = l_Lean_Meta_matchConstructorApp_x3f(x_511, x_499, x_500, x_501, x_502, x_515);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
lean_dec(x_516);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec_ref(x_517);
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_519;
goto block_465;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_520 = lean_ctor_get(x_516, 0);
lean_inc_ref(x_520);
lean_dec(x_516);
x_521 = lean_ctor_get(x_518, 0);
lean_inc(x_521);
lean_dec_ref(x_518);
x_522 = lean_ctor_get(x_521, 0);
lean_inc_ref(x_522);
lean_dec(x_521);
x_523 = lean_ctor_get(x_517, 1);
lean_inc(x_523);
lean_dec_ref(x_517);
x_524 = lean_ctor_get(x_520, 0);
lean_inc(x_524);
lean_dec_ref(x_520);
x_525 = lean_ctor_get(x_522, 0);
lean_inc(x_525);
lean_dec_ref(x_522);
x_526 = lean_name_eq(x_524, x_525);
lean_dec(x_525);
lean_dec(x_524);
if (x_526 == 0)
{
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_466 = x_500;
x_467 = x_501;
x_468 = x_502;
x_469 = x_499;
x_470 = x_523;
goto block_497;
}
else
{
if (x_16 == 0)
{
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_523;
goto block_465;
}
else
{
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_466 = x_500;
x_467 = x_501;
x_468 = x_502;
x_469 = x_499;
x_470 = x_523;
goto block_497;
}
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_516);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_527 = !lean_is_exclusive(x_517);
if (x_527 == 0)
{
return x_517;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_517, 0);
x_529 = lean_ctor_get(x_517, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_517);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_511);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_531 = !lean_is_exclusive(x_512);
if (x_531 == 0)
{
return x_512;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_512, 0);
x_533 = lean_ctor_get(x_512, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_512);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
}
else
{
uint8_t x_535; 
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_535 = !lean_is_exclusive(x_504);
if (x_535 == 0)
{
return x_504;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_504, 0);
x_537 = lean_ctor_get(x_504, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_504);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
block_681:
{
lean_object* x_546; 
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc_ref(x_540);
x_546 = l_Lean_Meta_matchNe_x3f(x_540, x_541, x_542, x_543, x_544, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; 
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_548;
goto block_539;
}
else
{
uint8_t x_549; 
x_549 = !lean_is_exclusive(x_547);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_550 = lean_ctor_get(x_547, 0);
x_551 = lean_ctor_get(x_550, 1);
lean_inc(x_551);
lean_dec(x_550);
x_552 = lean_ctor_get(x_546, 1);
lean_inc(x_552);
lean_dec_ref(x_546);
x_553 = !lean_is_exclusive(x_551);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_551, 0);
x_555 = lean_ctor_get(x_551, 1);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_554);
x_556 = l_Lean_Meta_isExprDefEq(x_554, x_555, x_541, x_542, x_543, x_544, x_552);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; uint8_t x_558; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_unbox(x_557);
lean_dec(x_557);
if (x_558 == 0)
{
lean_object* x_559; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
x_559 = lean_ctor_get(x_556, 1);
lean_inc(x_559);
lean_dec_ref(x_556);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_559;
goto block_539;
}
else
{
lean_object* x_560; lean_object* x_561; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
lean_dec_ref(x_556);
lean_inc(x_1);
x_561 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_560);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec_ref(x_561);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_564 = l_Lean_Meta_mkEqRefl(x_554, x_541, x_542, x_543, x_544, x_563);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec_ref(x_564);
x_567 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_568 = l_Lean_Meta_mkAbsurd(x_562, x_565, x_567, x_541, x_542, x_543, x_544, x_566);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec_ref(x_568);
x_571 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_569, x_542, x_570);
lean_dec(x_542);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_571, 0);
lean_dec(x_573);
x_574 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_551, 1, x_2);
lean_ctor_set(x_551, 0, x_574);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_551);
lean_ctor_set(x_571, 0, x_547);
return x_571;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_571, 1);
lean_inc(x_575);
lean_dec(x_571);
x_576 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_551, 1, x_2);
lean_ctor_set(x_551, 0, x_576);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_551);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_547);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
}
else
{
uint8_t x_578; 
lean_free_object(x_551);
lean_free_object(x_547);
lean_dec(x_542);
lean_dec(x_1);
x_578 = !lean_is_exclusive(x_568);
if (x_578 == 0)
{
return x_568;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_568, 0);
x_580 = lean_ctor_get(x_568, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_568);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec(x_562);
lean_free_object(x_551);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_564);
if (x_582 == 0)
{
return x_564;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_564, 0);
x_584 = lean_ctor_get(x_564, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_564);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
uint8_t x_586; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_586 = !lean_is_exclusive(x_561);
if (x_586 == 0)
{
return x_561;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_561, 0);
x_588 = lean_ctor_get(x_561, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_561);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
}
else
{
uint8_t x_590; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_590 = !lean_is_exclusive(x_556);
if (x_590 == 0)
{
return x_556;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_556, 0);
x_592 = lean_ctor_get(x_556, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_556);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_551, 0);
x_595 = lean_ctor_get(x_551, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_551);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_594);
x_596 = l_Lean_Meta_isExprDefEq(x_594, x_595, x_541, x_542, x_543, x_544, x_552);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; uint8_t x_598; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_unbox(x_597);
lean_dec(x_597);
if (x_598 == 0)
{
lean_object* x_599; 
lean_dec(x_594);
lean_free_object(x_547);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
lean_dec_ref(x_596);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_599;
goto block_539;
}
else
{
lean_object* x_600; lean_object* x_601; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_600 = lean_ctor_get(x_596, 1);
lean_inc(x_600);
lean_dec_ref(x_596);
lean_inc(x_1);
x_601 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec_ref(x_601);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_604 = l_Lean_Meta_mkEqRefl(x_594, x_541, x_542, x_543, x_544, x_603);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec_ref(x_604);
x_607 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_608 = l_Lean_Meta_mkAbsurd(x_602, x_605, x_607, x_541, x_542, x_543, x_544, x_606);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec_ref(x_608);
x_611 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_609, x_542, x_610);
lean_dec(x_542);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_613 = x_611;
} else {
 lean_dec_ref(x_611);
 x_613 = lean_box(0);
}
x_614 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_2);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_615);
if (lean_is_scalar(x_613)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_613;
}
lean_ctor_set(x_616, 0, x_547);
lean_ctor_set(x_616, 1, x_612);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_free_object(x_547);
lean_dec(x_542);
lean_dec(x_1);
x_617 = lean_ctor_get(x_608, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_608, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_619 = x_608;
} else {
 lean_dec_ref(x_608);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_602);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_621 = lean_ctor_get(x_604, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_604, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_623 = x_604;
} else {
 lean_dec_ref(x_604);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_594);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_625 = lean_ctor_get(x_601, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_601, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_627 = x_601;
} else {
 lean_dec_ref(x_601);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_594);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_629 = lean_ctor_get(x_596, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_596, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_631 = x_596;
} else {
 lean_dec_ref(x_596);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_547, 0);
lean_inc(x_633);
lean_dec(x_547);
x_634 = lean_ctor_get(x_633, 1);
lean_inc(x_634);
lean_dec(x_633);
x_635 = lean_ctor_get(x_546, 1);
lean_inc(x_635);
lean_dec_ref(x_546);
x_636 = lean_ctor_get(x_634, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_634, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_638 = x_634;
} else {
 lean_dec_ref(x_634);
 x_638 = lean_box(0);
}
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_636);
x_639 = l_Lean_Meta_isExprDefEq(x_636, x_637, x_541, x_542, x_543, x_544, x_635);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; uint8_t x_641; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_unbox(x_640);
lean_dec(x_640);
if (x_641 == 0)
{
lean_object* x_642; 
lean_dec(x_638);
lean_dec(x_636);
x_642 = lean_ctor_get(x_639, 1);
lean_inc(x_642);
lean_dec_ref(x_639);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_642;
goto block_539;
}
else
{
lean_object* x_643; lean_object* x_644; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_643 = lean_ctor_get(x_639, 1);
lean_inc(x_643);
lean_dec_ref(x_639);
lean_inc(x_1);
x_644 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_643);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec_ref(x_644);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_647 = l_Lean_Meta_mkEqRefl(x_636, x_541, x_542, x_543, x_544, x_646);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec_ref(x_647);
x_650 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_651 = l_Lean_Meta_mkAbsurd(x_645, x_648, x_650, x_541, x_542, x_543, x_544, x_649);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec_ref(x_651);
x_654 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_652, x_542, x_653);
lean_dec(x_542);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
x_657 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_638)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_638;
}
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_2);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
if (lean_is_scalar(x_656)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_656;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_655);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_638);
lean_dec(x_542);
lean_dec(x_1);
x_661 = lean_ctor_get(x_651, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_651, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_663 = x_651;
} else {
 lean_dec_ref(x_651);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_645);
lean_dec(x_638);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_665 = lean_ctor_get(x_647, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_647, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_667 = x_647;
} else {
 lean_dec_ref(x_647);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_669 = lean_ctor_get(x_644, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_644, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_671 = x_644;
} else {
 lean_dec_ref(x_644);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_673 = lean_ctor_get(x_639, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_639, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_675 = x_639;
} else {
 lean_dec_ref(x_639);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
}
}
else
{
uint8_t x_677; 
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_677 = !lean_is_exclusive(x_546);
if (x_677 == 0)
{
return x_546;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_546, 0);
x_679 = lean_ctor_get(x_546, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_546);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
block_753:
{
lean_object* x_683; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_682);
x_683 = l_Lean_Meta_matchNot_x3f(x_682, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec_ref(x_683);
x_540 = x_682;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_685;
goto block_681;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_683, 1);
lean_inc(x_686);
lean_dec_ref(x_683);
x_687 = lean_ctor_get(x_684, 0);
lean_inc(x_687);
lean_dec_ref(x_684);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_688 = l_Lean_Meta_findLocalDeclWithType_x3f(x_687, x_7, x_8, x_9, x_10, x_686);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; 
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec_ref(x_688);
x_540 = x_682;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_690;
goto block_681;
}
else
{
lean_object* x_691; uint8_t x_692; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_691 = lean_ctor_get(x_688, 1);
lean_inc(x_691);
lean_dec_ref(x_688);
x_692 = !lean_is_exclusive(x_689);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
x_693 = lean_ctor_get(x_689, 0);
lean_inc(x_1);
x_694 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_691);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec_ref(x_694);
x_697 = l_Lean_LocalDecl_toExpr(x_14);
x_698 = l_Lean_Expr_fvar___override(x_693);
x_699 = l_Lean_Expr_app___override(x_697, x_698);
lean_inc(x_8);
x_700 = l_Lean_Meta_mkFalseElim(x_695, x_699, x_7, x_8, x_9, x_10, x_696);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec_ref(x_700);
x_703 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_701, x_8, x_702);
lean_dec(x_8);
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_703, 0);
lean_dec(x_705);
x_706 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_2);
lean_ctor_set_tag(x_689, 0);
lean_ctor_set(x_689, 0, x_707);
lean_ctor_set(x_703, 0, x_689);
return x_703;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = lean_ctor_get(x_703, 1);
lean_inc(x_708);
lean_dec(x_703);
x_709 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_2);
lean_ctor_set_tag(x_689, 0);
lean_ctor_set(x_689, 0, x_710);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_689);
lean_ctor_set(x_711, 1, x_708);
return x_711;
}
}
else
{
uint8_t x_712; 
lean_free_object(x_689);
lean_dec(x_8);
lean_dec(x_1);
x_712 = !lean_is_exclusive(x_700);
if (x_712 == 0)
{
return x_700;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_700, 0);
x_714 = lean_ctor_get(x_700, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_700);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_free_object(x_689);
lean_dec(x_693);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_716 = !lean_is_exclusive(x_694);
if (x_716 == 0)
{
return x_694;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_694, 0);
x_718 = lean_ctor_get(x_694, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_694);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
else
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_689, 0);
lean_inc(x_720);
lean_dec(x_689);
lean_inc(x_1);
x_721 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_691);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec_ref(x_721);
x_724 = l_Lean_LocalDecl_toExpr(x_14);
x_725 = l_Lean_Expr_fvar___override(x_720);
x_726 = l_Lean_Expr_app___override(x_724, x_725);
lean_inc(x_8);
x_727 = l_Lean_Meta_mkFalseElim(x_722, x_726, x_7, x_8, x_9, x_10, x_723);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec_ref(x_727);
x_730 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_728, x_8, x_729);
lean_dec(x_8);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_732 = x_730;
} else {
 lean_dec_ref(x_730);
 x_732 = lean_box(0);
}
x_733 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_2);
x_735 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_735, 0, x_734);
if (lean_is_scalar(x_732)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_732;
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_731);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_8);
lean_dec(x_1);
x_737 = lean_ctor_get(x_727, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_727, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_739 = x_727;
} else {
 lean_dec_ref(x_727);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_720);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_741 = lean_ctor_get(x_721, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_721, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_743 = x_721;
} else {
 lean_dec_ref(x_721);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
}
}
else
{
uint8_t x_745; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_688);
if (x_745 == 0)
{
return x_688;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_688, 0);
x_747 = lean_ctor_get(x_688, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_688);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
}
else
{
uint8_t x_749; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_749 = !lean_is_exclusive(x_683);
if (x_749 == 0)
{
return x_683;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_683, 0);
x_751 = lean_ctor_get(x_683, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_683);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_751);
return x_752;
}
}
}
}
else
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_15)) {
 x_755 = lean_alloc_ctor(1, 1, 0);
} else {
 x_755 = x_15;
}
lean_ctor_set(x_755, 0, x_4);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_11);
return x_756;
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
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_357; uint8_t x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_682; lean_object* x_754; 
x_17 = 1;
x_754 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_754);
x_682 = x_754;
goto block_753;
block_48:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec_ref(x_3);
x_25 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_1, x_23, x_24, x_22, x_20, x_21, x_19, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
if (lean_is_scalar(x_15)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_15;
}
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
if (lean_is_scalar(x_15)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_15;
}
lean_ctor_set(x_32, 0, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_4);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_15;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
if (lean_is_scalar(x_15)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_15;
 lean_ctor_set_tag(x_42, 0);
}
lean_ctor_set(x_42, 0, x_41);
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
lean_dec(x_15);
lean_dec_ref(x_4);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
block_55:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_18 = x_49;
x_19 = x_51;
x_20 = x_50;
x_21 = x_52;
x_22 = x_53;
x_23 = x_54;
goto block_48;
}
block_64:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
else
{
x_49 = x_56;
x_50 = x_58;
x_51 = x_57;
x_52 = x_59;
x_53 = x_60;
goto block_55;
}
}
block_71:
{
if (x_66 == 0)
{
x_49 = x_65;
x_50 = x_67;
x_51 = x_68;
x_52 = x_69;
x_53 = x_70;
goto block_55;
}
else
{
x_56 = x_65;
x_57 = x_68;
x_58 = x_67;
x_59 = x_69;
x_60 = x_70;
x_61 = x_16;
goto block_64;
}
}
block_79:
{
if (x_78 == 0)
{
x_56 = x_72;
x_57 = x_75;
x_58 = x_74;
x_59 = x_76;
x_60 = x_77;
x_61 = x_16;
goto block_64;
}
else
{
x_65 = x_72;
x_66 = x_73;
x_67 = x_74;
x_68 = x_75;
x_69 = x_76;
x_70 = x_77;
goto block_71;
}
}
block_88:
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_87 == 0)
{
x_72 = x_86;
x_73 = x_80;
x_74 = x_83;
x_75 = x_85;
x_76 = x_84;
x_77 = x_82;
x_78 = x_16;
goto block_79;
}
else
{
if (x_81 == 0)
{
x_65 = x_86;
x_66 = x_80;
x_67 = x_83;
x_68 = x_85;
x_69 = x_84;
x_70 = x_82;
goto block_71;
}
else
{
x_72 = x_86;
x_73 = x_80;
x_74 = x_83;
x_75 = x_85;
x_76 = x_84;
x_77 = x_82;
x_78 = x_16;
goto block_79;
}
}
}
block_115:
{
if (x_96 == 0)
{
x_80 = x_90;
x_81 = x_92;
x_82 = x_95;
x_83 = x_94;
x_84 = x_89;
x_85 = x_91;
x_86 = x_93;
goto block_88;
}
else
{
lean_object* x_97; 
lean_inc(x_91);
lean_inc_ref(x_89);
lean_inc(x_94);
lean_inc_ref(x_95);
lean_inc(x_14);
lean_inc(x_1);
x_97 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_1, x_14, x_95, x_94, x_89, x_91, x_93);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec_ref(x_97);
x_80 = x_90;
x_81 = x_92;
x_82 = x_95;
x_83 = x_94;
x_84 = x_89;
x_85 = x_91;
x_86 = x_100;
goto block_88;
}
else
{
uint8_t x_101; 
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_91);
lean_dec_ref(x_89);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_dec(x_102);
x_103 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_2);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_97, 0, x_105);
return x_97;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_dec(x_97);
x_107 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_2);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_91);
lean_dec_ref(x_89);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_97);
if (x_111 == 0)
{
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
block_126:
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
if (x_124 == 0)
{
lean_dec_ref(x_117);
x_89 = x_121;
x_90 = x_116;
x_91 = x_122;
x_92 = x_118;
x_93 = x_123;
x_94 = x_120;
x_95 = x_119;
x_96 = x_16;
goto block_115;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_117);
x_89 = x_121;
x_90 = x_116;
x_91 = x_122;
x_92 = x_118;
x_93 = x_123;
x_94 = x_120;
x_95 = x_119;
x_96 = x_125;
goto block_115;
}
}
block_138:
{
if (x_136 == 0)
{
lean_dec_ref(x_132);
x_116 = x_127;
x_117 = x_128;
x_118 = x_131;
x_119 = x_129;
x_120 = x_133;
x_121 = x_135;
x_122 = x_134;
x_123 = x_130;
goto block_126;
}
else
{
lean_object* x_137; 
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
}
block_150:
{
uint8_t x_148; 
x_148 = l_Lean_Exception_isInterrupt(x_146);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Exception_isRuntime(x_146);
x_127 = x_139;
x_128 = x_141;
x_129 = x_140;
x_130 = x_147;
x_131 = x_142;
x_132 = x_146;
x_133 = x_143;
x_134 = x_144;
x_135 = x_145;
x_136 = x_149;
goto block_138;
}
else
{
x_127 = x_139;
x_128 = x_141;
x_129 = x_140;
x_130 = x_147;
x_131 = x_142;
x_132 = x_146;
x_133 = x_143;
x_134 = x_144;
x_135 = x_145;
x_136 = x_148;
goto block_138;
}
}
block_312:
{
lean_object* x_159; 
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc_ref(x_152);
lean_inc_ref(x_153);
x_159 = l_Lean_Meta_mkDecide(x_153, x_152, x_156, x_158, x_157, x_155);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = l_Lean_Meta_Context_config(x_152);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_164 = lean_ctor_get_uint8(x_152, sizeof(void*)*7);
x_165 = lean_ctor_get(x_152, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_152, 2);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_152, 3);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_152, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_152, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_152, 6);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_152, sizeof(void*)*7 + 1);
x_172 = lean_ctor_get_uint8(x_152, sizeof(void*)*7 + 2);
x_173 = 1;
lean_ctor_set_uint8(x_162, 9, x_173);
x_174 = l_Lean_Meta_Context_configKey(x_152);
x_175 = 2;
x_176 = lean_uint64_shift_right(x_174, x_175);
x_177 = lean_uint64_shift_left(x_176, x_175);
x_178 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_179 = lean_uint64_lor(x_177, x_178);
x_180 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set_uint64(x_180, sizeof(void*)*1, x_179);
x_181 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_165);
lean_ctor_set(x_181, 2, x_166);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_168);
lean_ctor_set(x_181, 5, x_169);
lean_ctor_set(x_181, 6, x_170);
lean_ctor_set_uint8(x_181, sizeof(void*)*7, x_164);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 1, x_171);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 2, x_172);
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc(x_160);
x_182 = lean_whnf(x_160, x_181, x_156, x_158, x_157, x_161);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
x_185 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_186 = l_Lean_Expr_isConstOf(x_183, x_185);
lean_dec(x_183);
if (x_186 == 0)
{
lean_dec(x_160);
x_116 = x_151;
x_117 = x_153;
x_118 = x_154;
x_119 = x_152;
x_120 = x_156;
x_121 = x_158;
x_122 = x_157;
x_123 = x_184;
goto block_126;
}
else
{
lean_object* x_187; 
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc_ref(x_152);
lean_inc(x_160);
x_187 = l_Lean_Meta_mkEqRefl(x_160, x_152, x_156, x_158, x_157, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
lean_inc(x_1);
x_190 = l_Lean_MVarId_getType(x_1, x_152, x_156, x_158, x_157, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
x_193 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_194 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_195 = l_Lean_Expr_getAppNumArgs(x_160);
lean_inc(x_195);
x_196 = lean_mk_array(x_195, x_194);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_sub(x_195, x_197);
lean_dec(x_195);
x_199 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_160, x_196, x_198);
x_200 = lean_array_push(x_199, x_188);
x_201 = l_Lean_mkAppN(x_193, x_200);
lean_dec_ref(x_200);
lean_inc(x_14);
x_202 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc_ref(x_152);
x_203 = l_Lean_Meta_mkAbsurd(x_191, x_202, x_201, x_152, x_156, x_158, x_157, x_192);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_205, x_156, x_206);
lean_dec(x_156);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
x_210 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 0, x_210);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_203);
lean_ctor_set(x_207, 0, x_211);
return x_207;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 0, x_213);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_203);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_203, 0);
x_217 = lean_ctor_get(x_203, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_203);
x_218 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_216, x_156, x_217);
lean_dec(x_156);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
x_221 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_2);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_220)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_220;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_219);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_203, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_203, 1);
lean_inc(x_226);
lean_dec_ref(x_203);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_225;
x_147 = x_226;
goto block_150;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_188);
lean_dec(x_160);
x_227 = lean_ctor_get(x_190, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_190, 1);
lean_inc(x_228);
lean_dec_ref(x_190);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_227;
x_147 = x_228;
goto block_150;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_160);
x_229 = lean_ctor_get(x_187, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_187, 1);
lean_inc(x_230);
lean_dec_ref(x_187);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_229;
x_147 = x_230;
goto block_150;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_160);
x_231 = lean_ctor_get(x_182, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_182, 1);
lean_inc(x_232);
lean_dec_ref(x_182);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_231;
x_147 = x_232;
goto block_150;
}
}
else
{
uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_233 = lean_ctor_get_uint8(x_162, 0);
x_234 = lean_ctor_get_uint8(x_162, 1);
x_235 = lean_ctor_get_uint8(x_162, 2);
x_236 = lean_ctor_get_uint8(x_162, 3);
x_237 = lean_ctor_get_uint8(x_162, 4);
x_238 = lean_ctor_get_uint8(x_162, 5);
x_239 = lean_ctor_get_uint8(x_162, 6);
x_240 = lean_ctor_get_uint8(x_162, 7);
x_241 = lean_ctor_get_uint8(x_162, 8);
x_242 = lean_ctor_get_uint8(x_162, 10);
x_243 = lean_ctor_get_uint8(x_162, 11);
x_244 = lean_ctor_get_uint8(x_162, 12);
x_245 = lean_ctor_get_uint8(x_162, 13);
x_246 = lean_ctor_get_uint8(x_162, 14);
x_247 = lean_ctor_get_uint8(x_162, 15);
x_248 = lean_ctor_get_uint8(x_162, 16);
x_249 = lean_ctor_get_uint8(x_162, 17);
x_250 = lean_ctor_get_uint8(x_162, 18);
lean_dec(x_162);
x_251 = lean_ctor_get_uint8(x_152, sizeof(void*)*7);
x_252 = lean_ctor_get(x_152, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_152, 2);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_152, 3);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_152, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_152, 5);
lean_inc(x_256);
x_257 = lean_ctor_get(x_152, 6);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_152, sizeof(void*)*7 + 1);
x_259 = lean_ctor_get_uint8(x_152, sizeof(void*)*7 + 2);
x_260 = 1;
x_261 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_261, 0, x_233);
lean_ctor_set_uint8(x_261, 1, x_234);
lean_ctor_set_uint8(x_261, 2, x_235);
lean_ctor_set_uint8(x_261, 3, x_236);
lean_ctor_set_uint8(x_261, 4, x_237);
lean_ctor_set_uint8(x_261, 5, x_238);
lean_ctor_set_uint8(x_261, 6, x_239);
lean_ctor_set_uint8(x_261, 7, x_240);
lean_ctor_set_uint8(x_261, 8, x_241);
lean_ctor_set_uint8(x_261, 9, x_260);
lean_ctor_set_uint8(x_261, 10, x_242);
lean_ctor_set_uint8(x_261, 11, x_243);
lean_ctor_set_uint8(x_261, 12, x_244);
lean_ctor_set_uint8(x_261, 13, x_245);
lean_ctor_set_uint8(x_261, 14, x_246);
lean_ctor_set_uint8(x_261, 15, x_247);
lean_ctor_set_uint8(x_261, 16, x_248);
lean_ctor_set_uint8(x_261, 17, x_249);
lean_ctor_set_uint8(x_261, 18, x_250);
x_262 = l_Lean_Meta_Context_configKey(x_152);
x_263 = 2;
x_264 = lean_uint64_shift_right(x_262, x_263);
x_265 = lean_uint64_shift_left(x_264, x_263);
x_266 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__1;
x_267 = lean_uint64_lor(x_265, x_266);
x_268 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_268, 0, x_261);
lean_ctor_set_uint64(x_268, sizeof(void*)*1, x_267);
x_269 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_252);
lean_ctor_set(x_269, 2, x_253);
lean_ctor_set(x_269, 3, x_254);
lean_ctor_set(x_269, 4, x_255);
lean_ctor_set(x_269, 5, x_256);
lean_ctor_set(x_269, 6, x_257);
lean_ctor_set_uint8(x_269, sizeof(void*)*7, x_251);
lean_ctor_set_uint8(x_269, sizeof(void*)*7 + 1, x_258);
lean_ctor_set_uint8(x_269, sizeof(void*)*7 + 2, x_259);
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc(x_160);
x_270 = lean_whnf(x_160, x_269, x_156, x_158, x_157, x_161);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__4;
x_274 = l_Lean_Expr_isConstOf(x_271, x_273);
lean_dec(x_271);
if (x_274 == 0)
{
lean_dec(x_160);
x_116 = x_151;
x_117 = x_153;
x_118 = x_154;
x_119 = x_152;
x_120 = x_156;
x_121 = x_158;
x_122 = x_157;
x_123 = x_272;
goto block_126;
}
else
{
lean_object* x_275; 
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc_ref(x_152);
lean_inc(x_160);
x_275 = l_Lean_Meta_mkEqRefl(x_160, x_152, x_156, x_158, x_157, x_272);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
lean_inc(x_1);
x_278 = l_Lean_MVarId_getType(x_1, x_152, x_156, x_158, x_157, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec_ref(x_278);
x_281 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__7;
x_282 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__8;
x_283 = l_Lean_Expr_getAppNumArgs(x_160);
lean_inc(x_283);
x_284 = lean_mk_array(x_283, x_282);
x_285 = lean_unsigned_to_nat(1u);
x_286 = lean_nat_sub(x_283, x_285);
lean_dec(x_283);
x_287 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_160, x_284, x_286);
x_288 = lean_array_push(x_287, x_276);
x_289 = l_Lean_mkAppN(x_281, x_288);
lean_dec_ref(x_288);
lean_inc(x_14);
x_290 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_157);
lean_inc_ref(x_158);
lean_inc(x_156);
lean_inc_ref(x_152);
x_291 = l_Lean_Meta_mkAbsurd(x_279, x_290, x_289, x_152, x_156, x_158, x_157, x_280);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
x_295 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_292, x_156, x_293);
lean_dec(x_156);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_294)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_294;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_2);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_299);
if (lean_is_scalar(x_297)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_297;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_296);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_291, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_291, 1);
lean_inc(x_303);
lean_dec_ref(x_291);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_302;
x_147 = x_303;
goto block_150;
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_276);
lean_dec(x_160);
x_304 = lean_ctor_get(x_278, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_278, 1);
lean_inc(x_305);
lean_dec_ref(x_278);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_304;
x_147 = x_305;
goto block_150;
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_160);
x_306 = lean_ctor_get(x_275, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_275, 1);
lean_inc(x_307);
lean_dec_ref(x_275);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_306;
x_147 = x_307;
goto block_150;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_160);
x_308 = lean_ctor_get(x_270, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_270, 1);
lean_inc(x_309);
lean_dec_ref(x_270);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_308;
x_147 = x_309;
goto block_150;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_159, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_159, 1);
lean_inc(x_311);
lean_dec_ref(x_159);
x_139 = x_151;
x_140 = x_152;
x_141 = x_153;
x_142 = x_154;
x_143 = x_156;
x_144 = x_157;
x_145 = x_158;
x_146 = x_310;
x_147 = x_311;
goto block_150;
}
}
block_322:
{
if (x_321 == 0)
{
x_116 = x_313;
x_117 = x_314;
x_118 = x_316;
x_119 = x_315;
x_120 = x_318;
x_121 = x_320;
x_122 = x_319;
x_123 = x_317;
goto block_126;
}
else
{
x_151 = x_313;
x_152 = x_315;
x_153 = x_314;
x_154 = x_316;
x_155 = x_317;
x_156 = x_318;
x_157 = x_319;
x_158 = x_320;
goto block_312;
}
}
block_333:
{
uint8_t x_332; 
x_332 = l_Lean_Expr_hasFVar(x_326);
lean_dec_ref(x_326);
if (x_332 == 0)
{
x_151 = x_323;
x_152 = x_325;
x_153 = x_324;
x_154 = x_328;
x_155 = x_327;
x_156 = x_329;
x_157 = x_330;
x_158 = x_331;
goto block_312;
}
else
{
x_313 = x_323;
x_314 = x_324;
x_315 = x_325;
x_316 = x_328;
x_317 = x_327;
x_318 = x_329;
x_319 = x_330;
x_320 = x_331;
x_321 = x_16;
goto block_322;
}
}
block_346:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_inc_ref(x_335);
x_342 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_335, x_338, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = l_Lean_Expr_hasMVar(x_343);
if (x_345 == 0)
{
x_323 = x_334;
x_324 = x_335;
x_325 = x_336;
x_326 = x_343;
x_327 = x_344;
x_328 = x_337;
x_329 = x_338;
x_330 = x_339;
x_331 = x_341;
goto block_333;
}
else
{
if (x_16 == 0)
{
lean_dec(x_343);
x_313 = x_334;
x_314 = x_335;
x_315 = x_336;
x_316 = x_337;
x_317 = x_344;
x_318 = x_338;
x_319 = x_339;
x_320 = x_341;
x_321 = x_16;
goto block_322;
}
else
{
x_323 = x_334;
x_324 = x_335;
x_325 = x_336;
x_326 = x_343;
x_327 = x_344;
x_328 = x_337;
x_329 = x_338;
x_330 = x_339;
x_331 = x_341;
goto block_333;
}
}
}
block_356:
{
if (x_355 == 0)
{
x_116 = x_347;
x_117 = x_348;
x_118 = x_350;
x_119 = x_349;
x_120 = x_351;
x_121 = x_354;
x_122 = x_352;
x_123 = x_353;
goto block_126;
}
else
{
x_334 = x_347;
x_335 = x_348;
x_336 = x_349;
x_337 = x_350;
x_338 = x_351;
x_339 = x_352;
x_340 = x_353;
x_341 = x_354;
goto block_346;
}
}
block_367:
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_365 == 0)
{
x_347 = x_359;
x_348 = x_357;
x_349 = x_360;
x_350 = x_358;
x_351 = x_361;
x_352 = x_363;
x_353 = x_364;
x_354 = x_362;
x_355 = x_16;
goto block_356;
}
else
{
uint8_t x_366; 
x_366 = l_Lean_Expr_hasFVar(x_357);
if (x_366 == 0)
{
x_334 = x_359;
x_335 = x_357;
x_336 = x_360;
x_337 = x_358;
x_338 = x_361;
x_339 = x_363;
x_340 = x_364;
x_341 = x_362;
goto block_346;
}
else
{
x_347 = x_359;
x_348 = x_357;
x_349 = x_360;
x_350 = x_358;
x_351 = x_361;
x_352 = x_363;
x_353 = x_364;
x_354 = x_362;
x_355 = x_16;
goto block_356;
}
}
}
block_419:
{
lean_object* x_377; 
lean_inc(x_374);
lean_inc_ref(x_369);
lean_inc(x_370);
lean_inc_ref(x_372);
x_377 = l_Lean_Meta_isExprDefEq(x_376, x_375, x_372, x_370, x_369, x_374, x_373);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_unbox(x_378);
lean_dec(x_378);
if (x_379 == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec_ref(x_377);
x_357 = x_368;
x_358 = x_371;
x_359 = x_17;
x_360 = x_372;
x_361 = x_370;
x_362 = x_369;
x_363 = x_374;
x_364 = x_380;
goto block_367;
}
else
{
lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_368);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_381 = lean_ctor_get(x_377, 1);
lean_inc(x_381);
lean_dec_ref(x_377);
lean_inc(x_1);
x_382 = l_Lean_MVarId_getType(x_1, x_372, x_370, x_369, x_374, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec_ref(x_382);
x_385 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_374);
lean_inc_ref(x_369);
lean_inc(x_370);
lean_inc_ref(x_372);
x_386 = l_Lean_Meta_mkEqOfHEq(x_385, x_17, x_372, x_370, x_369, x_374, x_384);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec_ref(x_386);
lean_inc(x_370);
x_389 = l_Lean_Meta_mkNoConfusion(x_383, x_387, x_372, x_370, x_369, x_374, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec_ref(x_389);
x_392 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_390, x_370, x_391);
lean_dec(x_370);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_392, 0);
lean_dec(x_394);
x_395 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_2);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_392, 0, x_397);
return x_392;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_398 = lean_ctor_get(x_392, 1);
lean_inc(x_398);
lean_dec(x_392);
x_399 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_2);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_398);
return x_402;
}
}
else
{
uint8_t x_403; 
lean_dec(x_370);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_389);
if (x_403 == 0)
{
return x_389;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_389, 0);
x_405 = lean_ctor_get(x_389, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_389);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_383);
lean_dec(x_374);
lean_dec_ref(x_372);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_386);
if (x_407 == 0)
{
return x_386;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_386, 0);
x_409 = lean_ctor_get(x_386, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_386);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_374);
lean_dec_ref(x_372);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_14);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_382);
if (x_411 == 0)
{
return x_382;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_382, 0);
x_413 = lean_ctor_get(x_382, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_382);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_374);
lean_dec_ref(x_372);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec_ref(x_368);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_377);
if (x_415 == 0)
{
return x_377;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_377, 0);
x_417 = lean_ctor_get(x_377, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_377);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
block_465:
{
lean_object* x_427; 
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
lean_inc_ref(x_420);
x_427 = l_Lean_Meta_matchHEq_x3f(x_420, x_422, x_423, x_424, x_425, x_426);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec_ref(x_427);
x_357 = x_420;
x_358 = x_421;
x_359 = x_16;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_429;
goto block_367;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
lean_dec_ref(x_428);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_427, 1);
lean_inc(x_433);
lean_dec_ref(x_427);
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
lean_dec(x_430);
x_435 = lean_ctor_get(x_431, 0);
lean_inc(x_435);
lean_dec(x_431);
x_436 = lean_ctor_get(x_432, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_432, 1);
lean_inc(x_437);
lean_dec(x_432);
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
x_438 = l_Lean_Meta_matchConstructorApp_x3f(x_435, x_422, x_423, x_424, x_425, x_433);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec_ref(x_438);
x_357 = x_420;
x_358 = x_421;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_440;
goto block_367;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec_ref(x_438);
x_442 = lean_ctor_get(x_439, 0);
lean_inc(x_442);
lean_dec_ref(x_439);
lean_inc(x_425);
lean_inc_ref(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
x_443 = l_Lean_Meta_matchConstructorApp_x3f(x_437, x_422, x_423, x_424, x_425, x_441);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
lean_dec(x_442);
lean_dec(x_436);
lean_dec(x_434);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec_ref(x_443);
x_357 = x_420;
x_358 = x_421;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_445;
goto block_367;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_446 = lean_ctor_get(x_442, 0);
lean_inc_ref(x_446);
lean_dec(x_442);
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
lean_dec_ref(x_444);
x_448 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_448);
lean_dec(x_447);
x_449 = lean_ctor_get(x_443, 1);
lean_inc(x_449);
lean_dec_ref(x_443);
x_450 = lean_ctor_get(x_446, 0);
lean_inc(x_450);
lean_dec_ref(x_446);
x_451 = lean_ctor_get(x_448, 0);
lean_inc(x_451);
lean_dec_ref(x_448);
x_452 = lean_name_eq(x_450, x_451);
lean_dec(x_451);
lean_dec(x_450);
if (x_452 == 0)
{
x_368 = x_420;
x_369 = x_424;
x_370 = x_423;
x_371 = x_421;
x_372 = x_422;
x_373 = x_449;
x_374 = x_425;
x_375 = x_436;
x_376 = x_434;
goto block_419;
}
else
{
if (x_16 == 0)
{
lean_dec(x_436);
lean_dec(x_434);
x_357 = x_420;
x_358 = x_421;
x_359 = x_17;
x_360 = x_422;
x_361 = x_423;
x_362 = x_424;
x_363 = x_425;
x_364 = x_449;
goto block_367;
}
else
{
x_368 = x_420;
x_369 = x_424;
x_370 = x_423;
x_371 = x_421;
x_372 = x_422;
x_373 = x_449;
x_374 = x_425;
x_375 = x_436;
x_376 = x_434;
goto block_419;
}
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_442);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_443);
if (x_453 == 0)
{
return x_443;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_443, 0);
x_455 = lean_ctor_get(x_443, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_443);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_457 = !lean_is_exclusive(x_438);
if (x_457 == 0)
{
return x_438;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_438, 0);
x_459 = lean_ctor_get(x_438, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_438);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_427);
if (x_461 == 0)
{
return x_427;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_427, 0);
x_463 = lean_ctor_get(x_427, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_427);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
block_497:
{
lean_object* x_471; 
lean_inc(x_1);
x_471 = l_Lean_MVarId_getType(x_1, x_469, x_468, x_470, x_467, x_466);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec_ref(x_471);
x_474 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_468);
x_475 = l_Lean_Meta_mkNoConfusion(x_472, x_474, x_469, x_468, x_470, x_467, x_473);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec_ref(x_475);
x_478 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_476, x_468, x_477);
lean_dec(x_468);
x_479 = !lean_is_exclusive(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_480 = lean_ctor_get(x_478, 0);
lean_dec(x_480);
x_481 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_2);
x_483 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_478, 0, x_483);
return x_478;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_478, 1);
lean_inc(x_484);
lean_dec(x_478);
x_485 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_2);
x_487 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_484);
return x_488;
}
}
else
{
uint8_t x_489; 
lean_dec(x_468);
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_475);
if (x_489 == 0)
{
return x_475;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_475, 0);
x_491 = lean_ctor_get(x_475, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_475);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
uint8_t x_493; 
lean_dec_ref(x_470);
lean_dec_ref(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_14);
lean_dec(x_1);
x_493 = !lean_is_exclusive(x_471);
if (x_493 == 0)
{
return x_471;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_471, 0);
x_495 = lean_ctor_get(x_471, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_471);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
block_539:
{
lean_object* x_504; 
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
lean_inc_ref(x_498);
x_504 = l_Lean_Meta_matchEq_x3f(x_498, x_499, x_500, x_501, x_502, x_503);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec_ref(x_504);
x_420 = x_498;
x_421 = x_16;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_506;
goto block_465;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
lean_dec_ref(x_505);
x_508 = lean_ctor_get(x_507, 1);
lean_inc(x_508);
lean_dec(x_507);
x_509 = lean_ctor_get(x_504, 1);
lean_inc(x_509);
lean_dec_ref(x_504);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
lean_dec(x_508);
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
x_512 = l_Lean_Meta_matchConstructorApp_x3f(x_510, x_499, x_500, x_501, x_502, x_509);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; 
lean_dec(x_511);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec_ref(x_512);
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_514;
goto block_465;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_515);
lean_dec_ref(x_512);
x_516 = lean_ctor_get(x_513, 0);
lean_inc(x_516);
lean_dec_ref(x_513);
lean_inc(x_502);
lean_inc_ref(x_501);
lean_inc(x_500);
lean_inc_ref(x_499);
x_517 = l_Lean_Meta_matchConstructorApp_x3f(x_511, x_499, x_500, x_501, x_502, x_515);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
lean_dec(x_516);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec_ref(x_517);
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_519;
goto block_465;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_520 = lean_ctor_get(x_516, 0);
lean_inc_ref(x_520);
lean_dec(x_516);
x_521 = lean_ctor_get(x_518, 0);
lean_inc(x_521);
lean_dec_ref(x_518);
x_522 = lean_ctor_get(x_521, 0);
lean_inc_ref(x_522);
lean_dec(x_521);
x_523 = lean_ctor_get(x_517, 1);
lean_inc(x_523);
lean_dec_ref(x_517);
x_524 = lean_ctor_get(x_520, 0);
lean_inc(x_524);
lean_dec_ref(x_520);
x_525 = lean_ctor_get(x_522, 0);
lean_inc(x_525);
lean_dec_ref(x_522);
x_526 = lean_name_eq(x_524, x_525);
lean_dec(x_525);
lean_dec(x_524);
if (x_526 == 0)
{
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_466 = x_523;
x_467 = x_502;
x_468 = x_500;
x_469 = x_499;
x_470 = x_501;
goto block_497;
}
else
{
if (x_16 == 0)
{
x_420 = x_498;
x_421 = x_17;
x_422 = x_499;
x_423 = x_500;
x_424 = x_501;
x_425 = x_502;
x_426 = x_523;
goto block_465;
}
else
{
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_466 = x_523;
x_467 = x_502;
x_468 = x_500;
x_469 = x_499;
x_470 = x_501;
goto block_497;
}
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_516);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_527 = !lean_is_exclusive(x_517);
if (x_527 == 0)
{
return x_517;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_517, 0);
x_529 = lean_ctor_get(x_517, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_517);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_511);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_531 = !lean_is_exclusive(x_512);
if (x_531 == 0)
{
return x_512;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_512, 0);
x_533 = lean_ctor_get(x_512, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_512);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
}
else
{
uint8_t x_535; 
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_535 = !lean_is_exclusive(x_504);
if (x_535 == 0)
{
return x_504;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_504, 0);
x_537 = lean_ctor_get(x_504, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_504);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
block_681:
{
lean_object* x_546; 
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc_ref(x_540);
x_546 = l_Lean_Meta_matchNe_x3f(x_540, x_541, x_542, x_543, x_544, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; 
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_548;
goto block_539;
}
else
{
uint8_t x_549; 
x_549 = !lean_is_exclusive(x_547);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_550 = lean_ctor_get(x_547, 0);
x_551 = lean_ctor_get(x_550, 1);
lean_inc(x_551);
lean_dec(x_550);
x_552 = lean_ctor_get(x_546, 1);
lean_inc(x_552);
lean_dec_ref(x_546);
x_553 = !lean_is_exclusive(x_551);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_551, 0);
x_555 = lean_ctor_get(x_551, 1);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_554);
x_556 = l_Lean_Meta_isExprDefEq(x_554, x_555, x_541, x_542, x_543, x_544, x_552);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; uint8_t x_558; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_unbox(x_557);
lean_dec(x_557);
if (x_558 == 0)
{
lean_object* x_559; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
x_559 = lean_ctor_get(x_556, 1);
lean_inc(x_559);
lean_dec_ref(x_556);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_559;
goto block_539;
}
else
{
lean_object* x_560; lean_object* x_561; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
lean_dec_ref(x_556);
lean_inc(x_1);
x_561 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_560);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec_ref(x_561);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_564 = l_Lean_Meta_mkEqRefl(x_554, x_541, x_542, x_543, x_544, x_563);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec_ref(x_564);
x_567 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_568 = l_Lean_Meta_mkAbsurd(x_562, x_565, x_567, x_541, x_542, x_543, x_544, x_566);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec_ref(x_568);
x_571 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_569, x_542, x_570);
lean_dec(x_542);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_571, 0);
lean_dec(x_573);
x_574 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_551, 1, x_2);
lean_ctor_set(x_551, 0, x_574);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_551);
lean_ctor_set(x_571, 0, x_547);
return x_571;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_571, 1);
lean_inc(x_575);
lean_dec(x_571);
x_576 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
lean_ctor_set(x_551, 1, x_2);
lean_ctor_set(x_551, 0, x_576);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_551);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_547);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
}
else
{
uint8_t x_578; 
lean_free_object(x_551);
lean_free_object(x_547);
lean_dec(x_542);
lean_dec(x_1);
x_578 = !lean_is_exclusive(x_568);
if (x_578 == 0)
{
return x_568;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_568, 0);
x_580 = lean_ctor_get(x_568, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_568);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec(x_562);
lean_free_object(x_551);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_564);
if (x_582 == 0)
{
return x_564;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_564, 0);
x_584 = lean_ctor_get(x_564, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_564);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
uint8_t x_586; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_586 = !lean_is_exclusive(x_561);
if (x_586 == 0)
{
return x_561;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_561, 0);
x_588 = lean_ctor_get(x_561, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_561);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
}
else
{
uint8_t x_590; 
lean_free_object(x_551);
lean_dec(x_554);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_590 = !lean_is_exclusive(x_556);
if (x_590 == 0)
{
return x_556;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_556, 0);
x_592 = lean_ctor_get(x_556, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_556);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_551, 0);
x_595 = lean_ctor_get(x_551, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_551);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_594);
x_596 = l_Lean_Meta_isExprDefEq(x_594, x_595, x_541, x_542, x_543, x_544, x_552);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; uint8_t x_598; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_unbox(x_597);
lean_dec(x_597);
if (x_598 == 0)
{
lean_object* x_599; 
lean_dec(x_594);
lean_free_object(x_547);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
lean_dec_ref(x_596);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_599;
goto block_539;
}
else
{
lean_object* x_600; lean_object* x_601; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_600 = lean_ctor_get(x_596, 1);
lean_inc(x_600);
lean_dec_ref(x_596);
lean_inc(x_1);
x_601 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec_ref(x_601);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_604 = l_Lean_Meta_mkEqRefl(x_594, x_541, x_542, x_543, x_544, x_603);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec_ref(x_604);
x_607 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_608 = l_Lean_Meta_mkAbsurd(x_602, x_605, x_607, x_541, x_542, x_543, x_544, x_606);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec_ref(x_608);
x_611 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_609, x_542, x_610);
lean_dec(x_542);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_613 = x_611;
} else {
 lean_dec_ref(x_611);
 x_613 = lean_box(0);
}
x_614 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_2);
lean_ctor_set_tag(x_547, 0);
lean_ctor_set(x_547, 0, x_615);
if (lean_is_scalar(x_613)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_613;
}
lean_ctor_set(x_616, 0, x_547);
lean_ctor_set(x_616, 1, x_612);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_free_object(x_547);
lean_dec(x_542);
lean_dec(x_1);
x_617 = lean_ctor_get(x_608, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_608, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_619 = x_608;
} else {
 lean_dec_ref(x_608);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_602);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_621 = lean_ctor_get(x_604, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_604, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_623 = x_604;
} else {
 lean_dec_ref(x_604);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_594);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_625 = lean_ctor_get(x_601, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_601, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_627 = x_601;
} else {
 lean_dec_ref(x_601);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_594);
lean_free_object(x_547);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_629 = lean_ctor_get(x_596, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_596, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_631 = x_596;
} else {
 lean_dec_ref(x_596);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_547, 0);
lean_inc(x_633);
lean_dec(x_547);
x_634 = lean_ctor_get(x_633, 1);
lean_inc(x_634);
lean_dec(x_633);
x_635 = lean_ctor_get(x_546, 1);
lean_inc(x_635);
lean_dec_ref(x_546);
x_636 = lean_ctor_get(x_634, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_634, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_638 = x_634;
} else {
 lean_dec_ref(x_634);
 x_638 = lean_box(0);
}
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_636);
x_639 = l_Lean_Meta_isExprDefEq(x_636, x_637, x_541, x_542, x_543, x_544, x_635);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; uint8_t x_641; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_unbox(x_640);
lean_dec(x_640);
if (x_641 == 0)
{
lean_object* x_642; 
lean_dec(x_638);
lean_dec(x_636);
x_642 = lean_ctor_get(x_639, 1);
lean_inc(x_642);
lean_dec_ref(x_639);
x_498 = x_540;
x_499 = x_541;
x_500 = x_542;
x_501 = x_543;
x_502 = x_544;
x_503 = x_642;
goto block_539;
}
else
{
lean_object* x_643; lean_object* x_644; 
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_643 = lean_ctor_get(x_639, 1);
lean_inc(x_643);
lean_dec_ref(x_639);
lean_inc(x_1);
x_644 = l_Lean_MVarId_getType(x_1, x_541, x_542, x_543, x_544, x_643);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec_ref(x_644);
lean_inc(x_544);
lean_inc_ref(x_543);
lean_inc(x_542);
lean_inc_ref(x_541);
x_647 = l_Lean_Meta_mkEqRefl(x_636, x_541, x_542, x_543, x_544, x_646);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec_ref(x_647);
x_650 = l_Lean_LocalDecl_toExpr(x_14);
lean_inc(x_542);
x_651 = l_Lean_Meta_mkAbsurd(x_645, x_648, x_650, x_541, x_542, x_543, x_544, x_649);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec_ref(x_651);
x_654 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_652, x_542, x_653);
lean_dec(x_542);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
x_657 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
if (lean_is_scalar(x_638)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_638;
}
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_2);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
if (lean_is_scalar(x_656)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_656;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_655);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_638);
lean_dec(x_542);
lean_dec(x_1);
x_661 = lean_ctor_get(x_651, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_651, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_663 = x_651;
} else {
 lean_dec_ref(x_651);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_645);
lean_dec(x_638);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_665 = lean_ctor_get(x_647, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_647, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_667 = x_647;
} else {
 lean_dec_ref(x_647);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_14);
lean_dec(x_1);
x_669 = lean_ctor_get(x_644, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_644, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_671 = x_644;
} else {
 lean_dec_ref(x_644);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_673 = lean_ctor_get(x_639, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_639, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_675 = x_639;
} else {
 lean_dec_ref(x_639);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
}
}
else
{
uint8_t x_677; 
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec_ref(x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_677 = !lean_is_exclusive(x_546);
if (x_677 == 0)
{
return x_546;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_546, 0);
x_679 = lean_ctor_get(x_546, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_546);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
block_753:
{
lean_object* x_683; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_682);
x_683 = l_Lean_Meta_matchNot_x3f(x_682, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec_ref(x_683);
x_540 = x_682;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_685;
goto block_681;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_683, 1);
lean_inc(x_686);
lean_dec_ref(x_683);
x_687 = lean_ctor_get(x_684, 0);
lean_inc(x_687);
lean_dec_ref(x_684);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_688 = l_Lean_Meta_findLocalDeclWithType_x3f(x_687, x_7, x_8, x_9, x_10, x_686);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; 
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec_ref(x_688);
x_540 = x_682;
x_541 = x_7;
x_542 = x_8;
x_543 = x_9;
x_544 = x_10;
x_545 = x_690;
goto block_681;
}
else
{
lean_object* x_691; uint8_t x_692; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_691 = lean_ctor_get(x_688, 1);
lean_inc(x_691);
lean_dec_ref(x_688);
x_692 = !lean_is_exclusive(x_689);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
x_693 = lean_ctor_get(x_689, 0);
lean_inc(x_1);
x_694 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_691);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec_ref(x_694);
x_697 = l_Lean_LocalDecl_toExpr(x_14);
x_698 = l_Lean_Expr_fvar___override(x_693);
x_699 = l_Lean_Expr_app___override(x_697, x_698);
lean_inc(x_8);
x_700 = l_Lean_Meta_mkFalseElim(x_695, x_699, x_7, x_8, x_9, x_10, x_696);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec_ref(x_700);
x_703 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_701, x_8, x_702);
lean_dec(x_8);
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_703, 0);
lean_dec(x_705);
x_706 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_2);
lean_ctor_set_tag(x_689, 0);
lean_ctor_set(x_689, 0, x_707);
lean_ctor_set(x_703, 0, x_689);
return x_703;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = lean_ctor_get(x_703, 1);
lean_inc(x_708);
lean_dec(x_703);
x_709 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_2);
lean_ctor_set_tag(x_689, 0);
lean_ctor_set(x_689, 0, x_710);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_689);
lean_ctor_set(x_711, 1, x_708);
return x_711;
}
}
else
{
uint8_t x_712; 
lean_free_object(x_689);
lean_dec(x_8);
lean_dec(x_1);
x_712 = !lean_is_exclusive(x_700);
if (x_712 == 0)
{
return x_700;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_700, 0);
x_714 = lean_ctor_get(x_700, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_700);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_free_object(x_689);
lean_dec(x_693);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_716 = !lean_is_exclusive(x_694);
if (x_716 == 0)
{
return x_694;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_694, 0);
x_718 = lean_ctor_get(x_694, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_694);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
else
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_689, 0);
lean_inc(x_720);
lean_dec(x_689);
lean_inc(x_1);
x_721 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_691);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec_ref(x_721);
x_724 = l_Lean_LocalDecl_toExpr(x_14);
x_725 = l_Lean_Expr_fvar___override(x_720);
x_726 = l_Lean_Expr_app___override(x_724, x_725);
lean_inc(x_8);
x_727 = l_Lean_Meta_mkFalseElim(x_722, x_726, x_7, x_8, x_9, x_10, x_723);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec_ref(x_727);
x_730 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_728, x_8, x_729);
lean_dec(x_8);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_732 = x_730;
} else {
 lean_dec_ref(x_730);
 x_732 = lean_box(0);
}
x_733 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_contradictionCore_spec__0_spec__0___lam__0___closed__0;
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_2);
x_735 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_735, 0, x_734);
if (lean_is_scalar(x_732)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_732;
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_731);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_8);
lean_dec(x_1);
x_737 = lean_ctor_get(x_727, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_727, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_739 = x_727;
} else {
 lean_dec_ref(x_727);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_720);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_741 = lean_ctor_get(x_721, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_721, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_743 = x_721;
} else {
 lean_dec_ref(x_721);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
}
}
else
{
uint8_t x_745; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_688);
if (x_745 == 0)
{
return x_688;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_688, 0);
x_747 = lean_ctor_get(x_688, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_688);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
}
else
{
uint8_t x_749; 
lean_dec_ref(x_682);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_749 = !lean_is_exclusive(x_683);
if (x_749 == 0)
{
return x_683;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_683, 0);
x_751 = lean_ctor_get(x_683, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_683);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_751);
return x_752;
}
}
}
}
else
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_15)) {
 x_755 = lean_alloc_ctor(1, 1, 0);
} else {
 x_755 = x_15;
}
lean_ctor_set(x_755, 0, x_4);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_11);
return x_756;
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
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__2;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Contradiction", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4436u);
x_2 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__4;
x_3 = 0;
x_4 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_;
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
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0);
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
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0);
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
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4436_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
