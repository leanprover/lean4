// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: Init Lean.Meta.MatchUtil Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Apply
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
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Contradiction_Config_searchFuel___default;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Contradiction_Config_emptyType___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
static lean_object* l_Lean_MVarId_contradictionCore___lambda__2___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_Lean_Meta_ElimEmptyInductive_elim___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_ACLt_main_lexSameCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeReaderT___rarg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1;
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_contradiction___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1;
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3;
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT uint8_t l_Lean_Meta_Contradiction_Config_genDiseq___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_contradiction___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__1;
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2;
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lean_MVarId_contradictionCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
static lean_object* l_Lean_MVarId_contradictionCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1;
static lean_object* l_Lean_MVarId_contradictionCore___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_contradictionCore___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7;
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2;
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15;
LEAN_EXPORT uint8_t l_Lean_Meta_Contradiction_Config_useDecide___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_Lean_Meta_Contradiction_Config_useDecide___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Contradiction_Config_emptyType___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Contradiction_Config_searchFuel___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(16u);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Contradiction_Config_genDiseq___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elim", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = l_Lean_Expr_hasLooseBVars(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___boxed), 1, 0);
return x_1;
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
x_11 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1;
x_12 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Meta_mkFalseElim(x_18, x_16, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_21, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
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
x_42 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1;
x_43 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_42, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lean_Expr_appArg_x21(x_47);
lean_dec(x_47);
lean_inc(x_1);
x_49 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lean_Meta_mkFalseElim(x_50, x_48, x_2, x_3, x_4, x_5, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_53, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_67 = x_49;
} else {
 lean_dec_ref(x_49);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_FVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_getAppFn(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_13);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_environment_find(x_19, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_List_lengthTRAux___rarg(x_25, x_26);
lean_dec(x_25);
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 2);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_nat_dec_lt(x_26, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
else
{
uint8_t x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = 1;
x_33 = lean_box(x_32);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_23);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_16, 0, x_35);
return x_16;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_environment_find(x_38, x_15);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
if (lean_obj_tag(x_43) == 5)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 4);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_List_lengthTRAux___rarg(x_45, x_46);
lean_dec(x_45);
x_48 = lean_nat_dec_eq(x_47, x_46);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_nat_dec_lt(x_46, x_49);
lean_dec(x_49);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_37);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_44);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_37);
return x_55;
}
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_43);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_37);
return x_58;
}
}
}
}
else
{
uint8_t x_59; lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_5);
x_59 = 0;
x_60 = lean_box(x_59);
lean_ctor_set(x_10, 0, x_60);
return x_10;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_10, 0);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_10);
x_63 = l_Lean_Expr_getAppFn(x_61);
lean_dec(x_61);
if (lean_obj_tag(x_63) == 4)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_5, x_62);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_environment_find(x_69, x_64);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 0;
x_72 = lean_box(x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
if (lean_obj_tag(x_74) == 5)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 4);
lean_inc(x_76);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_List_lengthTRAux___rarg(x_76, x_77);
lean_dec(x_76);
x_79 = lean_nat_dec_eq(x_78, x_77);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 2);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_nat_dec_lt(x_77, x_80);
lean_dec(x_80);
x_82 = lean_box(x_81);
if (lean_is_scalar(x_68)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_68;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
return x_83;
}
else
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_75);
x_84 = 1;
x_85 = lean_box(x_84);
if (lean_is_scalar(x_68)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_68;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_67);
return x_86;
}
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_74);
x_87 = 0;
x_88 = lean_box(x_87);
if (lean_is_scalar(x_68)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_68;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_67);
return x_89;
}
}
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_63);
lean_dec(x_5);
x_90 = 0;
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_62);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_10);
if (x_93 == 0)
{
return x_10;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_10, 0);
x_95 = lean_ctor_get(x_10, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_10);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_7);
if (x_97 == 0)
{
return x_7;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_7, 0);
x_99 = lean_ctor_get(x_7, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_7);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SavedState_restore(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_saveState___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2;
x_2 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_5, 2);
x_13 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_11, x_12, x_1);
lean_dec(x_11);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_5, 2);
x_18 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_15, x_17, x_1);
lean_dec(x_15);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1() {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_7);
x_16 = lean_array_uget(x_4, x_6);
x_26 = lean_ctor_get(x_2, 2);
x_27 = l_Lean_Meta_FVarSubst_apply(x_26, x_16);
x_28 = l_Lean_Expr_isFVar(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_inc(x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_17 = x_29;
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_fvarId_x21(x_27);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_30);
x_31 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_30, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_17 = x_35;
x_18 = x_34;
goto block_25;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_37 = l_Lean_Meta_ElimEmptyInductive_elim(x_3, x_30, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_17 = x_41;
x_18 = x_40;
goto block_25;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_17 = x_43;
x_18 = x_42;
goto block_25;
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
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
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_31, 0);
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_31);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_6 = x_23;
x_7 = x_21;
x_13 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_2, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1;
x_10 = lean_box(0);
x_11 = lean_apply_7(x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_box_usize(x_19);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1;
lean_inc(x_16);
lean_inc_n(x_1, 2);
x_22 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___boxed), 13, 7);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_16);
lean_closure_set(x_22, 3, x_17);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_1);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_MVarId_withContext___at_Lean_Meta_ElimEmptyInductive_elim___spec__4___rarg(x_16, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3;
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; size_t x_35; size_t x_36; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_add(x_4, x_35);
lean_inc(x_1);
{
size_t _tmp_3 = x_36;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_10 = x_34;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_14, 3);
x_18 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1;
x_19 = 0;
x_20 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_19);
lean_inc(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_PersistentArray_push___rarg(x_17, x_21);
lean_ctor_set(x_14, 3, x_22);
x_23 = lean_st_ref_set(x_7, x_14, x_15);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
x_32 = lean_ctor_get(x_14, 2);
x_33 = lean_ctor_get(x_14, 3);
x_34 = lean_ctor_get(x_14, 4);
x_35 = lean_ctor_get(x_14, 5);
x_36 = lean_ctor_get(x_14, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_37 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1;
x_38 = 0;
x_39 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_11);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_38);
lean_inc(x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_PersistentArray_push___rarg(x_33, x_40);
x_42 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_42, 6, x_36);
x_43 = lean_st_ref_set(x_7, x_42, x_15);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_Lean_Meta_ElimEmptyInductive_elim___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_28; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
lean_dec(x_42);
x_43 = 1;
x_44 = lean_box(x_43);
lean_ctor_set(x_28, 0, x_44);
return x_28;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_28, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_12 = x_49;
x_13 = x_50;
goto block_27;
}
block_27:
{
uint8_t x_14; 
x_14 = l_Lean_Exception_isRuntime(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
x_15 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_11)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_11;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_11);
x_22 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1() {
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
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5(x_12, x_1, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2;
x_18 = lean_box(0);
x_19 = lean_apply_7(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("contradiction", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1;
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2;
x_3 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elimEmptyInductive, number subgoals: ", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_array_get_size(x_1);
x_17 = l_Nat_repr(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_8, x_23, x_2, x_3, x_4, x_5, x_6, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2(x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_25);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = l_Lean_Exception_isRuntime(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_10);
x_24 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_24, x_4, x_5, x_6, x_7, x_8, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1;
x_29 = lean_unbox(x_26);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = lean_apply_7(x_28, x_30, x_4, x_5, x_6, x_7, x_8, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = l_Lean_Exception_toMessageData(x_21);
x_33 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_24, x_35, x_4, x_5, x_6, x_7, x_8, x_27);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_7(x_28, x_37, x_4, x_5, x_6, x_7, x_8, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_40 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_10);
x_41 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_42 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_41, x_4, x_5, x_6, x_7, x_8, x_22);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1;
x_46 = lean_unbox(x_43);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_21);
x_47 = lean_box(0);
x_48 = lean_apply_7(x_45, x_47, x_4, x_5, x_6, x_7, x_8, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = l_Lean_Exception_toMessageData(x_21);
x_50 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_41, x_52, x_4, x_5, x_6, x_7, x_8, x_44);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_apply_7(x_45, x_54, x_4, x_5, x_6, x_7, x_8, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_10);
x_59 = l_Lean_Exception_isRuntime(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_61 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_60, x_4, x_5, x_6, x_7, x_8, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1;
x_65 = lean_unbox(x_62);
lean_dec(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_57);
x_66 = lean_box(0);
x_67 = lean_apply_7(x_64, x_66, x_4, x_5, x_6, x_7, x_8, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = l_Lean_Exception_toMessageData(x_57);
x_69 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_60, x_71, x_4, x_5, x_6, x_7, x_8, x_63);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_apply_7(x_64, x_73, x_4, x_5, x_6, x_7, x_8, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_57);
lean_ctor_set(x_77, 1, x_58);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_79 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_78, x_4, x_5, x_6, x_7, x_8, x_58);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1;
x_83 = lean_unbox(x_80);
lean_dec(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_57);
x_84 = lean_box(0);
x_85 = lean_apply_7(x_82, x_84, x_4, x_5, x_6, x_7, x_8, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = l_Lean_Exception_toMessageData(x_57);
x_87 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_78, x_89, x_4, x_5, x_6, x_7, x_8, x_81);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_apply_7(x_82, x_91, x_4, x_5, x_6, x_7, x_8, x_92);
return x_93;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_7(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = lean_st_ref_set(x_4, x_14, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1;
x_18 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1;
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lambda__5), 9, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lambda__6), 8, 1);
lean_closure_set(x_20, 0, x_17);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_ElimEmptyInductive_elim___spec__3___rarg), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_commitWhen___at_Lean_Meta_ElimEmptyInductive_elim___spec__7(x_21, x_4, x_5, x_6, x_7, x_8, x_16);
return x_22;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elimEmptyInductive out-of-fuel", 30);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__7(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1;
x_21 = lean_unbox(x_18);
lean_dec(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_apply_7(x_20, x_22, x_3, x_4, x_5, x_6, x_7, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l_Lean_Meta_ElimEmptyInductive_elim___closed__2;
x_25 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_16, x_24, x_3, x_4, x_5, x_6, x_7, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_7(x_20, x_26, x_3, x_4, x_5, x_6, x_7, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_27; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
lean_dec(x_41);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_27, 0, x_43);
return x_27;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_27, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_dec(x_27);
x_11 = x_48;
x_12 = x_49;
goto block_26;
}
block_26:
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_10)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_10;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_10);
x_21 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_MVarId_exfalso(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_ElimEmptyInductive_elim(x_10, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 0;
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
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__1), 8, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_1);
x_22 = l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(x_21, x_4, x_5, x_6, x_7, x_20);
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
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lambda__2), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isEq(x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_isHEq(x_3);
x_9 = lean_box(x_8);
x_10 = lean_array_push(x_2, x_9);
x_1 = x_4;
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_array_push(x_2, x_13);
x_1 = x_4;
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_array_push(x_2, x_17);
x_1 = x_4;
x_2 = x_18;
goto _start;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_matchHEq_x3f(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_mkHEqRefl(x_26, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_isExprDefEq(x_1, x_28, x_5, x_6, x_7, x_8, x_29);
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
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
lean_dec(x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_3);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_30, 0, x_46);
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_3);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_30);
if (x_51 == 0)
{
return x_30;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
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
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_23; 
x_13 = lean_array_uget(x_2, x_4);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_5);
x_14 = x_30;
x_15 = x_10;
goto block_22;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_array_fget(x_26, x_27);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_27, x_37);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_38);
if (x_36 == 0)
{
lean_object* x_39; 
lean_dec(x_13);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_5);
x_14 = x_39;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_40; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_40 = lean_infer_type(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_matchEq_x3f(x_41, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_5);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_47 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_24, x_46, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_14 = x_48;
x_15 = x_49;
goto block_22;
}
else
{
uint8_t x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_dec(x_43);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_58 = l_Lean_Meta_mkEqRefl(x_57, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_61 = l_Lean_Meta_isExprDefEq(x_13, x_59, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
lean_ctor_set(x_5, 0, x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_5);
x_14 = x_66;
x_15 = x_64;
goto block_22;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_5);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_69 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_24, x_68, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_14 = x_70;
x_15 = x_71;
goto block_22;
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_61);
if (x_76 == 0)
{
return x_61;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_61, 0);
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_61);
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
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_58);
if (x_80 == 0)
{
return x_58;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
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
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
return x_43;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_43, 0);
x_86 = lean_ctor_get(x_43, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_43);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_40);
if (x_88 == 0)
{
return x_40;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_40, 0);
x_90 = lean_ctor_get(x_40, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_40);
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
lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_24);
x_92 = lean_array_fget(x_26, x_27);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_27, x_94);
lean_dec(x_27);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_26);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_28);
if (x_93 == 0)
{
lean_object* x_97; 
lean_dec(x_13);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_96);
lean_ctor_set(x_5, 0, x_1);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_5);
x_14 = x_97;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_98; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_98 = lean_infer_type(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_101 = l_Lean_Meta_matchEq_x3f(x_99, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_5);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_105 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_96, x_104, x_6, x_7, x_8, x_9, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_14 = x_106;
x_15 = x_107;
goto block_22;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_102, 0);
lean_inc(x_112);
lean_dec(x_102);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_116 = l_Lean_Meta_mkEqRefl(x_115, x_6, x_7, x_8, x_9, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_119 = l_Lean_Meta_isExprDefEq(x_13, x_117, x_6, x_7, x_8, x_9, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_13);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
lean_ctor_set(x_5, 1, x_96);
lean_ctor_set(x_5, 0, x_123);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_5);
x_14 = x_124;
x_15 = x_122;
goto block_22;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_5);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_127 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_96, x_126, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_14 = x_128;
x_15 = x_129;
goto block_22;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
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
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_134 = lean_ctor_get(x_119, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
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
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_138 = lean_ctor_get(x_116, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_116, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_140 = x_116;
} else {
 lean_dec_ref(x_116);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_142 = lean_ctor_get(x_101, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_101, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_144 = x_101;
} else {
 lean_dec_ref(x_101);
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
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_146 = lean_ctor_get(x_98, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_98, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_148 = x_98;
} else {
 lean_dec_ref(x_98);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_5, 1);
lean_inc(x_150);
lean_dec(x_5);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 2);
lean_inc(x_153);
x_154 = lean_nat_dec_lt(x_152, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_13);
lean_inc(x_1);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_150);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_14 = x_156;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
x_158 = lean_array_fget(x_151, x_152);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_152, x_160);
lean_dec(x_152);
if (lean_is_scalar(x_157)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_157;
}
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_153);
if (x_159 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_13);
lean_inc(x_1);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_14 = x_164;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_165; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_165 = lean_infer_type(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_168 = l_Lean_Meta_matchEq_x3f(x_166, x_6, x_7, x_8, x_9, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_172 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_162, x_171, x_6, x_7, x_8, x_9, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_14 = x_173;
x_15 = x_174;
goto block_22;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
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
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
lean_dec(x_169);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_ctor_get(x_168, 1);
lean_inc(x_181);
lean_dec(x_168);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_183 = l_Lean_Meta_mkEqRefl(x_182, x_6, x_7, x_8, x_9, x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_186 = l_Lean_Meta_isExprDefEq(x_13, x_184, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_13);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1;
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_162);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_14 = x_192;
x_15 = x_189;
goto block_22;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_186, 1);
lean_inc(x_193);
lean_dec(x_186);
x_194 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_195 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_13, x_1, x_162, x_194, x_6, x_7, x_8, x_9, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_14 = x_196;
x_15 = x_197;
goto block_22;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_162);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_202 = lean_ctor_get(x_186, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_204 = x_186;
} else {
 lean_dec_ref(x_186);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_162);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_206 = lean_ctor_get(x_183, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_183, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_208 = x_183;
} else {
 lean_dec_ref(x_183);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_162);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_210 = lean_ctor_get(x_168, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_168, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_212 = x_168;
} else {
 lean_dec_ref(x_168);
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
lean_dec(x_162);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_214 = lean_ctor_get(x_165, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_165, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_216 = x_165;
} else {
 lean_dec_ref(x_165);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
}
block_22:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_5 = x_18;
x_10 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkFalseElim(x_10, x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_11 = l_Lean_LocalDecl_toExpr(x_1);
lean_dec(x_1);
x_12 = l_Lean_mkAppN(x_11, x_2);
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_12, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1(x_3, x_14, x_20, x_6, x_7, x_8, x_9, x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_forallMetaTelescope(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask(x_1);
lean_dec(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_toSubarray___rarg(x_14, x_16, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_get_size(x_13);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1(x_18, x_13, x_21, x_22, x_19, x_4, x_5, x_6, x_7, x_12);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__2(x_2, x_13, x_3, x_18, x_27, x_4, x_5, x_6, x_7, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isGenDiseq localDecl.type\n  ", 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Tactic.Contradiction", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Meta.Tactic.Contradiction.0.Lean.Meta.processGenDiseq", 67);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5;
x_3 = lean_unsigned_to_nat(114u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_LocalDecl_type(x_2);
x_9 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6;
x_11 = l_panic___at_Lean_Meta_ACLt_main_lexSameCtor___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__3), 8, 3);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
x_13 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_12, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(x_13);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_7, x_9);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_18, x_20, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_20);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
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
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_39);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_18, x_39, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_39);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
lean_inc(x_6);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_9, x_50);
x_9 = x_51;
x_10 = x_49;
x_15 = x_47;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_LocalDecl_fvarId(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_6, x_16, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
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
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_12);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_6);
x_20 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_6, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_24, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_5);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1() {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("of_decide_eq_false", 18);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasFVar(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_6);
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_6, x_9, x_10, x_11, x_12, x_13);
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
x_22 = l_Lean_Expr_hasMVar(x_19);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasFVar(x_19);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_35; lean_object* x_36; lean_object* x_43; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_43 = l_Lean_Meta_mkDecide(x_6, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_9, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_9, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_9, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_9, 5);
lean_inc(x_51);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_53 = 1;
lean_ctor_set_uint8(x_44, 9, x_53);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set(x_54, 5, x_51);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_45);
x_55 = lean_whnf(x_45, x_54, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4;
x_59 = l_Lean_Expr_isConstOf(x_56, x_58);
lean_dec(x_56);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_45);
x_60 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_60;
x_25 = x_57;
goto block_34;
}
else
{
lean_object* x_61; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_45);
x_61 = l_Lean_Meta_mkEqRefl(x_45, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_45, x_64);
x_66 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8;
lean_inc(x_65);
x_67 = lean_mk_array(x_65, x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_65, x_68);
lean_dec(x_65);
x_70 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_45, x_67, x_69);
x_71 = lean_array_push(x_70, x_62);
x_72 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7;
x_73 = l_Lean_mkAppN(x_72, x_71);
lean_inc(x_5);
x_74 = l_Lean_MVarId_getType(x_5, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_LocalDecl_toExpr(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_78 = l_Lean_Meta_mkAbsurd(x_75, x_77, x_73, x_9, x_10, x_11, x_12, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_5);
x_81 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_5, x_79, x_9, x_10, x_11, x_12, x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9;
x_24 = x_83;
x_25 = x_82;
goto block_34;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_35 = x_84;
x_36 = x_85;
goto block_42;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_73);
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
lean_dec(x_74);
x_35 = x_86;
x_36 = x_87;
goto block_42;
}
}
else
{
uint8_t x_88; 
lean_dec(x_45);
x_88 = !lean_is_exclusive(x_61);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_61, 0);
x_90 = lean_ctor_get(x_61, 1);
x_91 = l_Lean_Exception_isRuntime(x_89);
if (x_91 == 0)
{
lean_object* x_92; 
lean_free_object(x_61);
lean_dec(x_89);
x_92 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_92;
x_25 = x_90;
goto block_34;
}
else
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_93 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
else
{
lean_object* x_94; 
lean_free_object(x_61);
lean_dec(x_89);
x_94 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_94;
x_25 = x_90;
goto block_34;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_61, 0);
x_96 = lean_ctor_get(x_61, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_61);
x_97 = l_Lean_Exception_isRuntime(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
x_98 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_98;
x_25 = x_96;
goto block_34;
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_95);
x_101 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_101;
x_25 = x_96;
goto block_34;
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_45);
x_102 = !lean_is_exclusive(x_55);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_55, 0);
x_104 = lean_ctor_get(x_55, 1);
x_105 = l_Lean_Exception_isRuntime(x_103);
if (x_105 == 0)
{
lean_object* x_106; 
lean_free_object(x_55);
lean_dec(x_103);
x_106 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_106;
x_25 = x_104;
goto block_34;
}
else
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_107 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_55;
}
else
{
lean_object* x_108; 
lean_free_object(x_55);
lean_dec(x_103);
x_108 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_108;
x_25 = x_104;
goto block_34;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_55, 0);
x_110 = lean_ctor_get(x_55, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_55);
x_111 = l_Lean_Exception_isRuntime(x_109);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_109);
x_112 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_112;
x_25 = x_110;
goto block_34;
}
else
{
uint8_t x_113; 
x_113 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_109);
x_115 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_115;
x_25 = x_110;
goto block_34;
}
}
}
}
}
else
{
uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get_uint8(x_44, 0);
x_117 = lean_ctor_get_uint8(x_44, 1);
x_118 = lean_ctor_get_uint8(x_44, 2);
x_119 = lean_ctor_get_uint8(x_44, 3);
x_120 = lean_ctor_get_uint8(x_44, 4);
x_121 = lean_ctor_get_uint8(x_44, 5);
x_122 = lean_ctor_get_uint8(x_44, 6);
x_123 = lean_ctor_get_uint8(x_44, 7);
x_124 = lean_ctor_get_uint8(x_44, 8);
x_125 = lean_ctor_get_uint8(x_44, 10);
x_126 = lean_ctor_get_uint8(x_44, 11);
lean_dec(x_44);
x_127 = 1;
x_128 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_128, 0, x_116);
lean_ctor_set_uint8(x_128, 1, x_117);
lean_ctor_set_uint8(x_128, 2, x_118);
lean_ctor_set_uint8(x_128, 3, x_119);
lean_ctor_set_uint8(x_128, 4, x_120);
lean_ctor_set_uint8(x_128, 5, x_121);
lean_ctor_set_uint8(x_128, 6, x_122);
lean_ctor_set_uint8(x_128, 7, x_123);
lean_ctor_set_uint8(x_128, 8, x_124);
lean_ctor_set_uint8(x_128, 9, x_127);
lean_ctor_set_uint8(x_128, 10, x_125);
lean_ctor_set_uint8(x_128, 11, x_126);
x_129 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_47);
lean_ctor_set(x_129, 2, x_48);
lean_ctor_set(x_129, 3, x_49);
lean_ctor_set(x_129, 4, x_50);
lean_ctor_set(x_129, 5, x_51);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_45);
x_130 = lean_whnf(x_45, x_129, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4;
x_134 = l_Lean_Expr_isConstOf(x_131, x_133);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_45);
x_135 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_135;
x_25 = x_132;
goto block_34;
}
else
{
lean_object* x_136; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_45);
x_136 = l_Lean_Meta_mkEqRefl(x_45, x_9, x_10, x_11, x_12, x_132);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_45, x_139);
x_141 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_140, x_143);
lean_dec(x_140);
x_145 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_45, x_142, x_144);
x_146 = lean_array_push(x_145, x_137);
x_147 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7;
x_148 = l_Lean_mkAppN(x_147, x_146);
lean_inc(x_5);
x_149 = l_Lean_MVarId_getType(x_5, x_9, x_10, x_11, x_12, x_138);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_LocalDecl_toExpr(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_153 = l_Lean_Meta_mkAbsurd(x_150, x_152, x_148, x_9, x_10, x_11, x_12, x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_5);
x_156 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_5, x_154, x_9, x_10, x_11, x_12, x_155);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9;
x_24 = x_158;
x_25 = x_157;
goto block_34;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_153, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_153, 1);
lean_inc(x_160);
lean_dec(x_153);
x_35 = x_159;
x_36 = x_160;
goto block_42;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_148);
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
lean_dec(x_149);
x_35 = x_161;
x_36 = x_162;
goto block_42;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_dec(x_45);
x_163 = lean_ctor_get(x_136, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_136, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_165 = x_136;
} else {
 lean_dec_ref(x_136);
 x_165 = lean_box(0);
}
x_166 = l_Lean_Exception_isRuntime(x_163);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_165);
lean_dec(x_163);
x_167 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_167;
x_25 = x_164;
goto block_34;
}
else
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_165)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_165;
}
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
else
{
lean_object* x_170; 
lean_dec(x_165);
lean_dec(x_163);
x_170 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_170;
x_25 = x_164;
goto block_34;
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_45);
x_171 = lean_ctor_get(x_130, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_130, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_173 = x_130;
} else {
 lean_dec_ref(x_130);
 x_173 = lean_box(0);
}
x_174 = l_Lean_Exception_isRuntime(x_171);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_173);
lean_dec(x_171);
x_175 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_175;
x_25 = x_172;
goto block_34;
}
else
{
uint8_t x_176; 
x_176 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_172);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_173);
lean_dec(x_171);
x_178 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_178;
x_25 = x_172;
goto block_34;
}
}
}
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_43);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_43, 0);
x_181 = lean_ctor_get(x_43, 1);
x_182 = l_Lean_Exception_isRuntime(x_180);
if (x_182 == 0)
{
lean_object* x_183; 
lean_free_object(x_43);
lean_dec(x_180);
x_183 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_183;
x_25 = x_181;
goto block_34;
}
else
{
uint8_t x_184; 
x_184 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_184 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
else
{
lean_object* x_185; 
lean_free_object(x_43);
lean_dec(x_180);
x_185 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_185;
x_25 = x_181;
goto block_34;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_43, 0);
x_187 = lean_ctor_get(x_43, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_43);
x_188 = l_Lean_Exception_isRuntime(x_186);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
x_189 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_189;
x_25 = x_187;
goto block_34;
}
else
{
uint8_t x_190; 
x_190 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_186);
x_192 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_192;
x_25 = x_187;
goto block_34;
}
}
}
}
block_34:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_26, x_9, x_10, x_11, x_12, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
if (lean_is_scalar(x_21)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_21;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
block_42:
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
x_38 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_38;
x_25 = x_36;
goto block_34;
}
else
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_35);
x_41 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1;
x_24 = x_41;
x_25 = x_36;
goto block_34;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_21);
x_193 = lean_box(0);
x_194 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_193, x_9, x_10, x_11, x_12, x_20);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_21);
lean_dec(x_19);
x_195 = lean_box(0);
x_196 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_195, x_9, x_10, x_11, x_12, x_20);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_box(0);
x_198 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_197, x_9, x_10, x_11, x_12, x_13);
return x_198;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_matchHEq_x3f(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_2, x_3, x_6, x_4, x_5, x_1, x_16, x_17, x_8, x_9, x_10, x_11, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Meta_matchConstructorApp_x3f(x_24, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = lean_box(0);
x_32 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_2, x_3, x_6, x_4, x_5, x_1, x_30, x_31, x_8, x_9, x_10, x_11, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l_Lean_Meta_matchConstructorApp_x3f(x_26, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_23);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 1;
x_39 = lean_box(0);
x_40 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_2, x_3, x_6, x_4, x_5, x_1, x_38, x_39, x_8, x_9, x_10, x_11, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_name_eq(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = l_Lean_Meta_isExprDefEq(x_23, x_25, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = 1;
x_53 = lean_box(0);
x_54 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_2, x_3, x_6, x_4, x_5, x_1, x_52, x_53, x_8, x_9, x_10, x_11, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
lean_inc(x_5);
x_56 = l_Lean_MVarId_getType(x_5, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalDecl_toExpr(x_4);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Meta_mkEqOfHEq(x_59, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_63 = l_Lean_Meta_mkNoConfusion(x_57, x_61, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_5, x_64, x_8, x_9, x_10, x_11, x_65);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_57);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
return x_60;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_60, 0);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_60);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
return x_56;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_56, 0);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_56);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_48);
if (x_85 == 0)
{
return x_48;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_48, 0);
x_87 = lean_ctor_get(x_48, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_48);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_25);
lean_dec(x_23);
x_89 = 1;
x_90 = lean_box(0);
x_91 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_2, x_3, x_6, x_4, x_5, x_1, x_89, x_90, x_8, x_9, x_10, x_11, x_41);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_35);
if (x_92 == 0)
{
return x_35;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_35, 0);
x_94 = lean_ctor_get(x_35, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_35);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_27);
if (x_96 == 0)
{
return x_27;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_27, 0);
x_98 = lean_ctor_get(x_27, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_27);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_13);
if (x_100 == 0)
{
return x_13;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_13, 0);
x_102 = lean_ctor_get(x_13, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_13);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_matchEq_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = lean_box(0);
x_17 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_7, x_8, x_9, x_10, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_Meta_matchConstructorApp_x3f(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_box(0);
x_28 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_5, x_26, x_27, x_7, x_8, x_9, x_10, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_matchConstructorApp_x3f(x_22, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 1;
x_35 = lean_box(0);
x_36 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_5, x_34, x_35, x_7, x_8, x_9, x_10, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_name_eq(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_5);
x_44 = l_Lean_MVarId_getType(x_5, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_LocalDecl_toExpr(x_4);
lean_dec(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Lean_Meta_mkNoConfusion(x_45, x_47, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_5, x_49, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
return x_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_66 = 1;
x_67 = lean_box(0);
x_68 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_5, x_66, x_67, x_7, x_8, x_9, x_10, x_37);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_31);
if (x_69 == 0)
{
return x_31;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_31, 0);
x_71 = lean_ctor_get(x_31, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_31);
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
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_23);
if (x_73 == 0)
{
return x_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_23, 0);
x_75 = lean_ctor_get(x_23, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_23);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_12);
if (x_77 == 0)
{
return x_12;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_matchNe_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__5(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_22 = l_Lean_Meta_isExprDefEq(x_20, x_21, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__5(x_1, x_2, x_3, x_4, x_5, x_26, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
lean_inc(x_5);
x_29 = l_Lean_MVarId_getType(x_5, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_Meta_mkEqRefl(x_20, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_LocalDecl_toExpr(x_4);
lean_dec(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Meta_mkAbsurd(x_30, x_33, x_35, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_5, x_37, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
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
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_array_uget(x_6, x_8);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_41; 
lean_inc(x_27);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_27);
x_29 = x_41;
x_30 = x_14;
goto block_40;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = l_Lean_LocalDecl_isImplementationDetail(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_LocalDecl_type(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
x_45 = l_Lean_Meta_matchNot_x3f(x_44, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_49 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(x_44, x_2, x_4, x_42, x_1, x_48, x_10, x_11, x_12, x_13, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_29 = x_50;
x_30 = x_51;
goto block_40;
}
else
{
uint8_t x_52; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
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
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
lean_dec(x_46);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_58 = l_Lean_Meta_findLocalDeclWithType_x3f(x_57, x_10, x_11, x_12, x_13, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_62 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(x_44, x_2, x_4, x_42, x_1, x_61, x_10, x_11, x_12, x_13, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_29 = x_63;
x_30 = x_64;
goto block_40;
}
else
{
uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_44);
x_69 = lean_ctor_get(x_58, 1);
lean_inc(x_69);
lean_dec(x_58);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
lean_dec(x_59);
lean_inc(x_1);
x_71 = l_Lean_MVarId_getType(x_1, x_10, x_11, x_12, x_13, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Expr_fvar___override(x_70);
x_75 = l_Lean_LocalDecl_toExpr(x_42);
lean_dec(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_76 = l_Lean_Meta_mkAbsurd(x_72, x_74, x_75, x_10, x_11, x_12, x_13, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_1);
x_79 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_77, x_10, x_11, x_12, x_13, x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_29 = x_81;
x_30 = x_80;
goto block_40;
}
else
{
uint8_t x_82; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_70);
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_71);
if (x_86 == 0)
{
return x_71;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_71, 0);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_71);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_58);
if (x_90 == 0)
{
return x_58;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_58, 0);
x_92 = lean_ctor_get(x_58, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_58);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_45);
if (x_94 == 0)
{
return x_45;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_45, 0);
x_96 = lean_ctor_get(x_45, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_45);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_42);
lean_inc(x_4);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_4);
x_29 = x_98;
x_30 = x_14;
goto block_40;
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_22;
x_14 = x_19;
goto _start;
}
}
block_40:
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_18 = x_33;
x_19 = x_30;
goto block_26;
}
else
{
uint8_t x_34; 
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_5);
if (lean_is_scalar(x_28)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_28;
}
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_29, 0, x_36);
x_18 = x_29;
x_19 = x_30;
goto block_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
lean_inc(x_5);
if (lean_is_scalar(x_28)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_28;
}
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_18 = x_39;
x_19 = x_30;
goto block_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_array_get_size(x_13);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_13, x_17, x_18, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1(x_23, x_24, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
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
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
lean_dec(x_5);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_array_get_size(x_36);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4(x_1, x_2, x_3, x_4, x_37, x_36, x_40, x_41, x_38, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_36);
lean_dec(x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1(x_46, x_47, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_array_uget(x_6, x_8);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_46; 
lean_inc(x_27);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_27);
x_29 = x_46;
x_30 = x_14;
goto block_45;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_17, 0);
lean_inc(x_47);
lean_dec(x_17);
x_48 = l_Lean_LocalDecl_isImplementationDetail(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_LocalDecl_type(x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_49);
x_50 = l_Lean_Meta_matchNot_x3f(x_49, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_54 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(x_49, x_2, x_4, x_47, x_1, x_53, x_10, x_11, x_12, x_13, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_29 = x_55;
x_30 = x_56;
goto block_45;
}
else
{
uint8_t x_57; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_63 = l_Lean_Meta_findLocalDeclWithType_x3f(x_62, x_10, x_11, x_12, x_13, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_67 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__6(x_49, x_2, x_4, x_47, x_1, x_66, x_10, x_11, x_12, x_13, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_29 = x_68;
x_30 = x_69;
goto block_45;
}
else
{
uint8_t x_70; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_49);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_dec(x_63);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
lean_inc(x_1);
x_76 = l_Lean_MVarId_getType(x_1, x_10, x_11, x_12, x_13, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_fvar___override(x_75);
x_80 = l_Lean_LocalDecl_toExpr(x_47);
lean_dec(x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_81 = l_Lean_Meta_mkAbsurd(x_77, x_79, x_80, x_10, x_11, x_12, x_13, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_1);
x_84 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_82, x_10, x_11, x_12, x_13, x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3;
x_29 = x_86;
x_30 = x_85;
goto block_45;
}
else
{
uint8_t x_87; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_75);
lean_dec(x_47);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_76);
if (x_91 == 0)
{
return x_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_76);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_63);
if (x_95 == 0)
{
return x_63;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_63, 0);
x_97 = lean_ctor_get(x_63, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_63);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_50);
if (x_99 == 0)
{
return x_50;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_50, 0);
x_101 = lean_ctor_get(x_50, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_50);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_47);
lean_inc(x_4);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_4);
x_29 = x_103;
x_30 = x_14;
goto block_45;
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_22;
x_14 = x_19;
goto _start;
}
}
block_45:
{
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_29, 0, x_34);
x_18 = x_29;
x_19 = x_30;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_28;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_18 = x_38;
x_19 = x_30;
goto block_26;
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_5);
if (lean_is_scalar(x_28)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_28;
}
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_29, 0, x_41);
x_18 = x_29;
x_19 = x_30;
goto block_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
lean_inc(x_5);
if (lean_is_scalar(x_28)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_28;
}
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_18 = x_44;
x_19 = x_30;
goto block_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_6, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_get_size(x_23);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5(x_1, x_2, x_3, x_4, x_24, x_23, x_27, x_28, x_25, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_23);
lean_dec(x_3);
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
lean_dec(x_31);
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
lean_dec(x_31);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_contradictionCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1(x_1, x_2, x_3, x_12, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_MVarId_contradictionCore___lambda__2___closed__1;
x_18 = lean_box(0);
x_19 = lean_apply_6(x_17, x_18, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_MVarId_contradictionCore___lambda__2(x_1, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_MVarId_contradictionCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_contradictionCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_contradictionCore___closed__1;
x_2 = l_ReaderT_instApplicativeReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_contradictionCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_contradictionCore___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlT__1___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_contradictionCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_MVarId_contradictionCore___closed__4;
x_9 = l_Lean_MVarId_contradictionCore___closed__3;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lambda__3), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_9);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_contradictionCore___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_contradictionCore___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_contradictionCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_contradictionCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_MVarId_contradiction___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_contradiction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_contradiction___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_8);
x_12 = l_Lean_MVarId_contradictionCore___closed__4;
x_13 = l_Lean_MVarId_contradiction___closed__2;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_13, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_contradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_contradiction(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2;
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8;
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9;
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Contradiction", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14;
x_2 = lean_unsigned_to_nat(4437u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Meta_Contradiction_Config_useDecide___default = _init_l_Lean_Meta_Contradiction_Config_useDecide___default();
l_Lean_Meta_Contradiction_Config_emptyType___default = _init_l_Lean_Meta_Contradiction_Config_emptyType___default();
l_Lean_Meta_Contradiction_Config_searchFuel___default = _init_l_Lean_Meta_Contradiction_Config_searchFuel___default();
lean_mark_persistent(l_Lean_Meta_Contradiction_Config_searchFuel___default);
l_Lean_Meta_Contradiction_Config_genDiseq___default = _init_l_Lean_Meta_Contradiction_Config_genDiseq___default();
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__1);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4 = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__4);
l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM = _init_l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM);
l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_ElimEmptyInductive_elim___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_ElimEmptyInductive_elim___spec__5___boxed__const__1);
l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_ElimEmptyInductive_elim___spec__6___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__2___closed__2);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__2);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__3);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__4);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__5);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__6);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__7);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__3___closed__8);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__4___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__5___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___lambda__7___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___closed__1 = _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___closed__1);
l_Lean_Meta_ElimEmptyInductive_elim___closed__2 = _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__2();
lean_mark_persistent(l_Lean_Meta_ElimEmptyInductive_elim___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___spec__1___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__4);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__5);
l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6 = _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__6);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_contradictionCore___spec__4___lambda__3___closed__9);
l_Lean_MVarId_contradictionCore___lambda__2___closed__1 = _init_l_Lean_MVarId_contradictionCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___lambda__2___closed__1);
l_Lean_MVarId_contradictionCore___closed__1 = _init_l_Lean_MVarId_contradictionCore___closed__1();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___closed__1);
l_Lean_MVarId_contradictionCore___closed__2 = _init_l_Lean_MVarId_contradictionCore___closed__2();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___closed__2);
l_Lean_MVarId_contradictionCore___closed__3 = _init_l_Lean_MVarId_contradictionCore___closed__3();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___closed__3);
l_Lean_MVarId_contradictionCore___closed__4 = _init_l_Lean_MVarId_contradictionCore___closed__4();
lean_mark_persistent(l_Lean_MVarId_contradictionCore___closed__4);
l_Lean_MVarId_contradiction___closed__1 = _init_l_Lean_MVarId_contradiction___closed__1();
lean_mark_persistent(l_Lean_MVarId_contradiction___closed__1);
l_Lean_MVarId_contradiction___closed__2 = _init_l_Lean_MVarId_contradiction___closed__2();
lean_mark_persistent(l_Lean_MVarId_contradiction___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437____closed__15);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Contradiction___hyg_4437_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
