// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Split
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.CasesMatch
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_introNewHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCaseSplitStatus;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5;
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedCaseSplitStatus;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4;
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5;
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEM(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34_(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1;
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lambda__4___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3;
lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCaseSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_11 = lean_nat_dec_eq(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
if (x_8 == 0)
{
if (x_10 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
return x_10;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_beqCaseSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_34____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqCaseSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = 0;
x_3 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Grind_isEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
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
x_26 = lean_box(0);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
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
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_11, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_11, 0, x_36);
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Grind_isEqFalse(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
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
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
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
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_dec(x_1);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = l_Lean_Meta_Grind_isEqTrue(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
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
x_41 = l_Lean_Meta_Grind_isEqTrue(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
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
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
x_48 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_41, 0, x_52);
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
return x_41;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
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
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_37);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_37, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_37, 0, x_62);
return x_37;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_37, 1);
lean_inc(x_63);
lean_dec(x_37);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_37);
if (x_66 == 0)
{
return x_37;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_37, 0);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_37);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
return x_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_13, 0);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Grind_isEqFalse(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
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
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_Grind_isEqFalse(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
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
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_27, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_27, 0, x_52);
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_dec(x_27);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_17);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_13, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_13, 0, x_66);
return x_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_dec(x_13);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
return x_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_13, 0);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_20; 
lean_inc(x_1);
x_20 = l_Lean_Meta_Grind_isEqTrue(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Grind_isEqFalse(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_box(1);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
lean_inc(x_2);
x_34 = l_Lean_Meta_Grind_isEqTrue(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_unbox(x_39);
lean_dec(x_39);
x_13 = x_42;
x_14 = x_41;
goto block_19;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_Meta_Grind_isEqTrue(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_13 = x_47;
x_14 = x_46;
goto block_19;
}
else
{
uint8_t x_48; 
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
else
{
uint8_t x_52; 
lean_dec(x_3);
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
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_dec(x_34);
lean_inc(x_3);
x_57 = l_Lean_Meta_Grind_isEqFalse(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_58);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_unbox(x_62);
lean_dec(x_62);
x_13 = x_65;
x_14 = x_64;
goto block_19;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = l_Lean_Meta_Grind_isEqTrue(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_13 = x_70;
x_14 = x_69;
goto block_19;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_61);
if (x_75 == 0)
{
return x_61;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_61, 0);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_61);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_dec(x_57);
x_80 = lean_unbox(x_58);
lean_dec(x_58);
x_13 = x_80;
x_14 = x_79;
goto block_19;
}
}
else
{
uint8_t x_81; 
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_57);
if (x_81 == 0)
{
return x_57;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_57, 0);
x_83 = lean_ctor_get(x_57, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_57);
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
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_34);
if (x_85 == 0)
{
return x_34;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_34, 0);
x_87 = lean_ctor_get(x_34, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_34);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_24);
if (x_89 == 0)
{
return x_24;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_24, 0);
x_91 = lean_ctor_get(x_24, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_24);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_93 = lean_ctor_get(x_20, 1);
lean_inc(x_93);
lean_dec(x_20);
lean_inc(x_2);
x_94 = l_Lean_Meta_Grind_isEqTrue(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_3);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_unbox(x_99);
lean_dec(x_99);
x_13 = x_102;
x_14 = x_101;
goto block_19;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = l_Lean_Meta_Grind_isEqFalse(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_unbox(x_105);
lean_dec(x_105);
x_13 = x_107;
x_14 = x_106;
goto block_19;
}
else
{
uint8_t x_108; 
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
}
else
{
uint8_t x_112; 
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_98);
if (x_112 == 0)
{
return x_98;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_98, 0);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_98);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_94, 1);
lean_inc(x_116);
lean_dec(x_94);
lean_inc(x_3);
x_117 = l_Lean_Meta_Grind_isEqTrue(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_3);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_unbox(x_122);
lean_dec(x_122);
x_13 = x_125;
x_14 = x_124;
goto block_19;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_122);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = l_Lean_Meta_Grind_isEqFalse(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_unbox(x_128);
lean_dec(x_128);
x_13 = x_130;
x_14 = x_129;
goto block_19;
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 0);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_127);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_3);
x_135 = !lean_is_exclusive(x_121);
if (x_135 == 0)
{
return x_121;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_121, 0);
x_137 = lean_ctor_get(x_121, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_121);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_117, 1);
lean_inc(x_139);
lean_dec(x_117);
x_140 = lean_unbox(x_118);
lean_dec(x_118);
x_13 = x_140;
x_14 = x_139;
goto block_19;
}
}
else
{
uint8_t x_141; 
lean_dec(x_3);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_117);
if (x_141 == 0)
{
return x_117;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_117, 0);
x_143 = lean_ctor_get(x_117, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_117);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_3);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_94);
if (x_145 == 0)
{
return x_94;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_94, 0);
x_147 = lean_ctor_get(x_94, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_94);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_20);
if (x_149 == 0)
{
return x_20;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_20, 0);
x_151 = lean_ctor_get(x_20, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_20);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
block_19:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4;
x_2 = l_Lean_Meta_Grind_instInhabitedCaseSplitStatus;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Split", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Split.0.Lean.Meta.Grind.checkCaseSplitStatus", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(90u);
x_4 = lean_unsigned_to_nat(43u);
x_5 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_isInductivePredicate_x3f(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5;
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_apply_10(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Meta_Grind_isEqTrue(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = lean_apply_10(x_17, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_21, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 4);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_List_lengthTRAux___rarg(x_29, x_30);
lean_dec(x_29);
x_32 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_dec(x_20);
x_33 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_20, 4);
lean_inc(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_List_lengthTRAux___rarg(x_35, x_36);
lean_dec(x_35);
x_38 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_dec(x_20);
x_39 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
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
lean_dec(x_12);
lean_dec(x_1);
x_49 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4;
x_50 = l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_isMatcherAppCore_x3f(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_12);
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_isMatcherAppCore_x3f(x_26, x_1);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split resolved: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_isResolvedCaseSplit(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_22);
lean_free_object(x_12);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_apply_10(x_26, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lean_MessageData_ofExpr(x_1);
x_31 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_30);
lean_ctor_set(x_22, 0, x_31);
x_32 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_22);
x_33 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_apply_10(x_26, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5;
x_40 = lean_unbox(x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_12);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_apply_10(x_39, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = l_Lean_MessageData_ofExpr(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_45);
x_47 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_apply_10(x_39, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4;
x_53 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
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
x_57 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5;
x_58 = lean_unbox(x_54);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_apply_10(x_57, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = l_Lean_MessageData_ofExpr(x_1);
x_62 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7;
if (lean_is_scalar(x_56)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_56;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_52, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_apply_10(x_57, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
return x_69;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Or", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1;
x_15 = l_Lean_Expr_cleanupAnnotations(x_12);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_20 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Expr_appArg(x_20, lean_box(0));
x_25 = l_Lean_Expr_appFnCleanup(x_20, lean_box(0));
x_26 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5;
x_29 = l_Lean_Expr_isConstOf(x_25, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isApp(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup(x_25, lean_box(0));
x_34 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_19);
x_36 = l_Lean_Expr_isApp(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Expr_appArg(x_33, lean_box(0));
x_40 = l_Lean_Expr_appFnCleanup(x_33, lean_box(0));
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Expr_appFnCleanup(x_40, lean_box(0));
x_45 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9;
x_46 = l_Lean_Expr_isConstOf(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11;
x_48 = l_Lean_Expr_isConstOf(x_44, x_47);
lean_dec(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = lean_apply_10(x_14, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_1);
x_52 = lean_apply_10(x_14, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_52;
}
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_33);
x_53 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(x_1, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_25);
x_54 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(x_1, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_25);
x_55 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(x_1, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_nat_dec_lt(x_1, x_2);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_getGeneration(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_getGeneration(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_nat_dec_lt(x_16, x_20);
lean_dec(x_20);
lean_dec(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_18);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2(x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_nat_dec_lt(x_16, x_27);
lean_dec(x_27);
lean_dec(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2(x_3, x_4, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
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
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 18);
lean_dec(x_17);
x_18 = l_List_reverse___rarg(x_3);
lean_ctor_set(x_14, 18, x_18);
x_19 = lean_st_ref_set(x_4, x_14, x_15);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_27 = lean_st_ref_get(x_4, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_71 = lean_ctor_get(x_28, 19);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_dec_lt(x_72, x_25);
lean_dec(x_25);
x_74 = lean_st_ref_take(x_4, x_29);
if (x_73 == 0)
{
if (x_26 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_30 = x_71;
x_31 = x_75;
x_32 = x_76;
goto block_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_nat_add(x_71, x_72);
lean_dec(x_71);
x_30 = x_79;
x_31 = x_77;
x_32 = x_78;
goto block_70;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_nat_add(x_71, x_72);
lean_dec(x_71);
x_30 = x_82;
x_31 = x_80;
x_32 = x_81;
goto block_70;
}
block_70:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_31, 19);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 14);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_31, 19, x_30);
lean_ctor_set(x_31, 14, x_36);
x_37 = lean_st_ref_set(x_4, x_31, x_32);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
x_44 = lean_ctor_get(x_31, 2);
x_45 = lean_ctor_get(x_31, 3);
x_46 = lean_ctor_get(x_31, 4);
x_47 = lean_ctor_get(x_31, 5);
x_48 = lean_ctor_get(x_31, 6);
x_49 = lean_ctor_get_uint8(x_31, sizeof(void*)*23);
x_50 = lean_ctor_get(x_31, 7);
x_51 = lean_ctor_get(x_31, 8);
x_52 = lean_ctor_get(x_31, 9);
x_53 = lean_ctor_get(x_31, 10);
x_54 = lean_ctor_get(x_31, 11);
x_55 = lean_ctor_get(x_31, 12);
x_56 = lean_ctor_get(x_31, 13);
x_57 = lean_ctor_get(x_31, 15);
x_58 = lean_ctor_get(x_31, 16);
x_59 = lean_ctor_get(x_31, 17);
x_60 = lean_ctor_get(x_31, 18);
x_61 = lean_ctor_get(x_31, 20);
x_62 = lean_ctor_get(x_31, 21);
x_63 = lean_ctor_get(x_31, 22);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_43);
lean_ctor_set(x_65, 2, x_44);
lean_ctor_set(x_65, 3, x_45);
lean_ctor_set(x_65, 4, x_46);
lean_ctor_set(x_65, 5, x_47);
lean_ctor_set(x_65, 6, x_48);
lean_ctor_set(x_65, 7, x_50);
lean_ctor_set(x_65, 8, x_51);
lean_ctor_set(x_65, 9, x_52);
lean_ctor_set(x_65, 10, x_53);
lean_ctor_set(x_65, 11, x_54);
lean_ctor_set(x_65, 12, x_55);
lean_ctor_set(x_65, 13, x_56);
lean_ctor_set(x_65, 14, x_64);
lean_ctor_set(x_65, 15, x_57);
lean_ctor_set(x_65, 16, x_58);
lean_ctor_set(x_65, 17, x_59);
lean_ctor_set(x_65, 18, x_60);
lean_ctor_set(x_65, 19, x_30);
lean_ctor_set(x_65, 20, x_61);
lean_ctor_set(x_65, 21, x_62);
lean_ctor_set(x_65, 22, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*23, x_49);
x_66 = lean_st_ref_set(x_4, x_65, x_32);
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_83 = lean_ctor_get(x_14, 0);
x_84 = lean_ctor_get(x_14, 1);
x_85 = lean_ctor_get(x_14, 2);
x_86 = lean_ctor_get(x_14, 3);
x_87 = lean_ctor_get(x_14, 4);
x_88 = lean_ctor_get(x_14, 5);
x_89 = lean_ctor_get(x_14, 6);
x_90 = lean_ctor_get_uint8(x_14, sizeof(void*)*23);
x_91 = lean_ctor_get(x_14, 7);
x_92 = lean_ctor_get(x_14, 8);
x_93 = lean_ctor_get(x_14, 9);
x_94 = lean_ctor_get(x_14, 10);
x_95 = lean_ctor_get(x_14, 11);
x_96 = lean_ctor_get(x_14, 12);
x_97 = lean_ctor_get(x_14, 13);
x_98 = lean_ctor_get(x_14, 14);
x_99 = lean_ctor_get(x_14, 15);
x_100 = lean_ctor_get(x_14, 16);
x_101 = lean_ctor_get(x_14, 17);
x_102 = lean_ctor_get(x_14, 19);
x_103 = lean_ctor_get(x_14, 20);
x_104 = lean_ctor_get(x_14, 21);
x_105 = lean_ctor_get(x_14, 22);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_14);
x_106 = l_List_reverse___rarg(x_3);
x_107 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_107, 0, x_83);
lean_ctor_set(x_107, 1, x_84);
lean_ctor_set(x_107, 2, x_85);
lean_ctor_set(x_107, 3, x_86);
lean_ctor_set(x_107, 4, x_87);
lean_ctor_set(x_107, 5, x_88);
lean_ctor_set(x_107, 6, x_89);
lean_ctor_set(x_107, 7, x_91);
lean_ctor_set(x_107, 8, x_92);
lean_ctor_set(x_107, 9, x_93);
lean_ctor_set(x_107, 10, x_94);
lean_ctor_set(x_107, 11, x_95);
lean_ctor_set(x_107, 12, x_96);
lean_ctor_set(x_107, 13, x_97);
lean_ctor_set(x_107, 14, x_98);
lean_ctor_set(x_107, 15, x_99);
lean_ctor_set(x_107, 16, x_100);
lean_ctor_set(x_107, 17, x_101);
lean_ctor_set(x_107, 18, x_106);
lean_ctor_set(x_107, 19, x_102);
lean_ctor_set(x_107, 20, x_103);
lean_ctor_set(x_107, 21, x_104);
lean_ctor_set(x_107, 22, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*23, x_90);
x_108 = lean_st_ref_set(x_4, x_107, x_15);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_4);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_115 = lean_st_ref_get(x_4, x_112);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_151 = lean_ctor_get(x_116, 19);
lean_inc(x_151);
lean_dec(x_116);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_dec_lt(x_152, x_113);
lean_dec(x_113);
x_154 = lean_st_ref_take(x_4, x_117);
if (x_153 == 0)
{
if (x_114 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_118 = x_151;
x_119 = x_155;
x_120 = x_156;
goto block_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
lean_dec(x_154);
x_159 = lean_nat_add(x_151, x_152);
lean_dec(x_151);
x_118 = x_159;
x_119 = x_157;
x_120 = x_158;
goto block_150;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_154, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
lean_dec(x_154);
x_162 = lean_nat_add(x_151, x_152);
lean_dec(x_151);
x_118 = x_162;
x_119 = x_160;
x_120 = x_161;
goto block_150;
}
block_150:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 5);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 6);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_119, sizeof(void*)*23);
x_129 = lean_ctor_get(x_119, 7);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 8);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 9);
lean_inc(x_131);
x_132 = lean_ctor_get(x_119, 10);
lean_inc(x_132);
x_133 = lean_ctor_get(x_119, 11);
lean_inc(x_133);
x_134 = lean_ctor_get(x_119, 12);
lean_inc(x_134);
x_135 = lean_ctor_get(x_119, 13);
lean_inc(x_135);
x_136 = lean_ctor_get(x_119, 15);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 16);
lean_inc(x_137);
x_138 = lean_ctor_get(x_119, 17);
lean_inc(x_138);
x_139 = lean_ctor_get(x_119, 18);
lean_inc(x_139);
x_140 = lean_ctor_get(x_119, 20);
lean_inc(x_140);
x_141 = lean_ctor_get(x_119, 21);
lean_inc(x_141);
x_142 = lean_ctor_get(x_119, 22);
lean_inc(x_142);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 lean_ctor_release(x_119, 7);
 lean_ctor_release(x_119, 8);
 lean_ctor_release(x_119, 9);
 lean_ctor_release(x_119, 10);
 lean_ctor_release(x_119, 11);
 lean_ctor_release(x_119, 12);
 lean_ctor_release(x_119, 13);
 lean_ctor_release(x_119, 14);
 lean_ctor_release(x_119, 15);
 lean_ctor_release(x_119, 16);
 lean_ctor_release(x_119, 17);
 lean_ctor_release(x_119, 18);
 lean_ctor_release(x_119, 19);
 lean_ctor_release(x_119, 20);
 lean_ctor_release(x_119, 21);
 lean_ctor_release(x_119, 22);
 x_143 = x_119;
} else {
 lean_dec_ref(x_119);
 x_143 = lean_box(0);
}
x_144 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 23, 1);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_121);
lean_ctor_set(x_145, 1, x_122);
lean_ctor_set(x_145, 2, x_123);
lean_ctor_set(x_145, 3, x_124);
lean_ctor_set(x_145, 4, x_125);
lean_ctor_set(x_145, 5, x_126);
lean_ctor_set(x_145, 6, x_127);
lean_ctor_set(x_145, 7, x_129);
lean_ctor_set(x_145, 8, x_130);
lean_ctor_set(x_145, 9, x_131);
lean_ctor_set(x_145, 10, x_132);
lean_ctor_set(x_145, 11, x_133);
lean_ctor_set(x_145, 12, x_134);
lean_ctor_set(x_145, 13, x_135);
lean_ctor_set(x_145, 14, x_144);
lean_ctor_set(x_145, 15, x_136);
lean_ctor_set(x_145, 16, x_137);
lean_ctor_set(x_145, 17, x_138);
lean_ctor_set(x_145, 18, x_139);
lean_ctor_set(x_145, 19, x_118);
lean_ctor_set(x_145, 20, x_140);
lean_ctor_set(x_145, 21, x_141);
lean_ctor_set(x_145, 22, x_142);
lean_ctor_set_uint8(x_145, sizeof(void*)*23, x_128);
x_146 = lean_st_ref_set(x_4, x_145, x_120);
lean_dec(x_4);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_2);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_1);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_1, 0);
x_165 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_164);
x_166 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus(x_164, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
switch (lean_obj_tag(x_167)) {
case 0:
{
lean_object* x_168; 
lean_free_object(x_1);
lean_dec(x_164);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_1 = x_165;
x_12 = x_168;
goto _start;
}
case 1:
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_170;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
lean_free_object(x_1);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_dec(x_166);
x_173 = lean_ctor_get(x_167, 0);
lean_inc(x_173);
x_174 = lean_ctor_get_uint8(x_167, sizeof(void*)*1);
lean_dec(x_167);
x_175 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_175, 0, x_164);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*2, x_174);
x_1 = x_165;
x_2 = x_175;
x_12 = x_172;
goto _start;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = lean_ctor_get(x_166, 1);
lean_inc(x_177);
lean_dec(x_166);
x_178 = lean_ctor_get(x_167, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_167, sizeof(void*)*1);
lean_dec(x_167);
x_180 = lean_ctor_get(x_2, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_dec_eq(x_178, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(0);
lean_inc(x_180);
lean_inc(x_164);
x_185 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_164, x_180, x_178, x_181, x_184, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_177);
lean_dec(x_181);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_180);
lean_dec(x_178);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_188;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_2);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_2, 1);
lean_dec(x_191);
x_192 = lean_ctor_get(x_2, 0);
lean_dec(x_192);
x_193 = lean_ctor_get(x_185, 1);
lean_inc(x_193);
lean_dec(x_185);
lean_ctor_set(x_2, 1, x_178);
lean_ctor_set(x_2, 0, x_164);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_193;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_195 = lean_ctor_get(x_185, 1);
lean_inc(x_195);
lean_dec(x_185);
x_196 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_196, 0, x_164);
lean_ctor_set(x_196, 1, x_178);
lean_ctor_set_uint8(x_196, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_1 = x_196;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_195;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_180);
lean_dec(x_178);
lean_free_object(x_1);
lean_dec(x_165);
lean_dec(x_164);
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
x_198 = !lean_is_exclusive(x_185);
if (x_198 == 0)
{
return x_185;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_185, 0);
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_185);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
if (x_179 == 0)
{
uint8_t x_202; 
x_202 = lean_nat_dec_lt(x_182, x_181);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_box(0);
lean_inc(x_180);
lean_inc(x_164);
x_204 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_164, x_180, x_178, x_181, x_203, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_177);
lean_dec(x_181);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec(x_180);
lean_dec(x_178);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_207;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_2);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_2, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_2, 0);
lean_dec(x_211);
x_212 = lean_ctor_get(x_204, 1);
lean_inc(x_212);
lean_dec(x_204);
lean_ctor_set(x_2, 1, x_178);
lean_ctor_set(x_2, 0, x_164);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_212;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_2);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_dec(x_204);
x_215 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_215, 0, x_164);
lean_ctor_set(x_215, 1, x_178);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_1 = x_215;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_214;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_180);
lean_dec(x_178);
lean_free_object(x_1);
lean_dec(x_165);
lean_dec(x_164);
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
x_217 = !lean_is_exclusive(x_204);
if (x_217 == 0)
{
return x_204;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_204, 0);
x_219 = lean_ctor_get(x_204, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_204);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_181);
x_221 = !lean_is_exclusive(x_2);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_2, 1);
lean_dec(x_222);
x_223 = lean_ctor_get(x_2, 0);
lean_dec(x_223);
lean_ctor_set(x_2, 1, x_178);
lean_ctor_set(x_2, 0, x_164);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_177;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_225; 
lean_dec(x_2);
x_225 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_225, 0, x_164);
lean_ctor_set(x_225, 1, x_178);
lean_ctor_set_uint8(x_225, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_1 = x_225;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_177;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_box(0);
lean_inc(x_180);
lean_inc(x_164);
x_228 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_164, x_180, x_178, x_181, x_227, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_177);
lean_dec(x_181);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_180);
lean_dec(x_178);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_231;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_2);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_2, 1);
lean_dec(x_234);
x_235 = lean_ctor_get(x_2, 0);
lean_dec(x_235);
x_236 = lean_ctor_get(x_228, 1);
lean_inc(x_236);
lean_dec(x_228);
lean_ctor_set(x_2, 1, x_178);
lean_ctor_set(x_2, 0, x_164);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_236;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_2);
x_238 = lean_ctor_get(x_228, 1);
lean_inc(x_238);
lean_dec(x_228);
x_239 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_239, 0, x_164);
lean_ctor_set(x_239, 1, x_178);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_179);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_180);
{
lean_object* _tmp_0 = x_165;
lean_object* _tmp_1 = x_239;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_11 = x_238;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_180);
lean_dec(x_178);
lean_free_object(x_1);
lean_dec(x_165);
lean_dec(x_164);
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
x_241 = !lean_is_exclusive(x_228);
if (x_241 == 0)
{
return x_228;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_228, 0);
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_228);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
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
uint8_t x_245; 
lean_free_object(x_1);
lean_dec(x_165);
lean_dec(x_164);
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
x_245 = !lean_is_exclusive(x_166);
if (x_245 == 0)
{
return x_166;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_166, 0);
x_247 = lean_ctor_get(x_166, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_166);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_1, 0);
x_250 = lean_ctor_get(x_1, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_249);
x_251 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus(x_249, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
switch (lean_obj_tag(x_252)) {
case 0:
{
lean_object* x_253; 
lean_dec(x_249);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_1 = x_250;
x_12 = x_253;
goto _start;
}
case 1:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_251, 1);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_249);
lean_ctor_set(x_256, 1, x_3);
x_1 = x_250;
x_3 = x_256;
x_12 = x_255;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_251, 1);
lean_inc(x_258);
lean_dec(x_251);
x_259 = lean_ctor_get(x_252, 0);
lean_inc(x_259);
x_260 = lean_ctor_get_uint8(x_252, sizeof(void*)*1);
lean_dec(x_252);
x_261 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_261, 0, x_249);
lean_ctor_set(x_261, 1, x_259);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_260);
x_1 = x_250;
x_2 = x_261;
x_12 = x_258;
goto _start;
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_263 = lean_ctor_get(x_251, 1);
lean_inc(x_263);
lean_dec(x_251);
x_264 = lean_ctor_get(x_252, 0);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_252, sizeof(void*)*1);
lean_dec(x_252);
x_266 = lean_ctor_get(x_2, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_2, 1);
lean_inc(x_267);
x_268 = lean_unsigned_to_nat(1u);
x_269 = lean_nat_dec_eq(x_264, x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_box(0);
lean_inc(x_266);
lean_inc(x_249);
x_271 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_249, x_266, x_264, x_267, x_270, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_263);
lean_dec(x_267);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_unbox(x_272);
lean_dec(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_266);
lean_dec(x_264);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_249);
lean_ctor_set(x_275, 1, x_3);
x_1 = x_250;
x_3 = x_275;
x_12 = x_274;
goto _start;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_277 = x_2;
} else {
 lean_dec_ref(x_2);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_271, 1);
lean_inc(x_278);
lean_dec(x_271);
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(1, 2, 1);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_249);
lean_ctor_set(x_279, 1, x_264);
lean_ctor_set_uint8(x_279, sizeof(void*)*2, x_265);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_266);
lean_ctor_set(x_280, 1, x_3);
x_1 = x_250;
x_2 = x_279;
x_3 = x_280;
x_12 = x_278;
goto _start;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_250);
lean_dec(x_249);
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
x_282 = lean_ctor_get(x_271, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_271, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_284 = x_271;
} else {
 lean_dec_ref(x_271);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
if (x_265 == 0)
{
uint8_t x_286; 
x_286 = lean_nat_dec_lt(x_268, x_267);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_box(0);
lean_inc(x_266);
lean_inc(x_249);
x_288 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_249, x_266, x_264, x_267, x_287, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_263);
lean_dec(x_267);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_266);
lean_dec(x_264);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_249);
lean_ctor_set(x_292, 1, x_3);
x_1 = x_250;
x_3 = x_292;
x_12 = x_291;
goto _start;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_294 = x_2;
} else {
 lean_dec_ref(x_2);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_288, 1);
lean_inc(x_295);
lean_dec(x_288);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(1, 2, 1);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_249);
lean_ctor_set(x_296, 1, x_264);
lean_ctor_set_uint8(x_296, sizeof(void*)*2, x_265);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_266);
lean_ctor_set(x_297, 1, x_3);
x_1 = x_250;
x_2 = x_296;
x_3 = x_297;
x_12 = x_295;
goto _start;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_250);
lean_dec(x_249);
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
x_299 = lean_ctor_get(x_288, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_288, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_301 = x_288;
} else {
 lean_dec_ref(x_288);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_267);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_303 = x_2;
} else {
 lean_dec_ref(x_2);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 1);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_249);
lean_ctor_set(x_304, 1, x_264);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_265);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_266);
lean_ctor_set(x_305, 1, x_3);
x_1 = x_250;
x_2 = x_304;
x_3 = x_305;
x_12 = x_263;
goto _start;
}
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_box(0);
lean_inc(x_266);
lean_inc(x_249);
x_308 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_249, x_266, x_264, x_267, x_307, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_263);
lean_dec(x_267);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_266);
lean_dec(x_264);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_249);
lean_ctor_set(x_312, 1, x_3);
x_1 = x_250;
x_3 = x_312;
x_12 = x_311;
goto _start;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_314 = x_2;
} else {
 lean_dec_ref(x_2);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
lean_dec(x_308);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(1, 2, 1);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_249);
lean_ctor_set(x_316, 1, x_264);
lean_ctor_set_uint8(x_316, sizeof(void*)*2, x_265);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_266);
lean_ctor_set(x_317, 1, x_3);
x_1 = x_250;
x_2 = x_316;
x_3 = x_317;
x_12 = x_315;
goto _start;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_250);
lean_dec(x_249);
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
x_319 = lean_ctor_get(x_308, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_308, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_321 = x_308;
} else {
 lean_dec_ref(x_308);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
}
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_250);
lean_dec(x_249);
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
x_323 = lean_ctor_get(x_251, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_251, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_325 = x_251;
} else {
 lean_dec_ref(x_251);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 18);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(x_14, x_16, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_checkMaxCaseSplit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1;
x_16 = lean_box(0);
x_17 = lean_apply_10(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_isInconsistent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1;
x_15 = lean_box(0);
x_16 = lean_apply_10(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_eq_eq_false", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_eq_eq_true", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5;
x_21 = l_Lean_mkApp3(x_20, x_2, x_3, x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5;
x_25 = l_Lean_mkApp3(x_24, x_2, x_3, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8;
x_36 = l_Lean_mkApp3(x_35, x_2, x_3, x_34);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8;
x_40 = l_Lean_mkApp3(x_39, x_2, x_3, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
uint8_t x_46; 
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
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkEM(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_of_and_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3;
x_17 = l_Lean_mkApp3(x_16, x_2, x_3, x_15);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3;
x_21 = l_Lean_mkApp3(x_20, x_2, x_3, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_14);
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
x_18 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
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
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
x_15 = l_Lean_Expr_cleanupAnnotations(x_12);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_20 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Expr_appArg(x_20, lean_box(0));
x_25 = l_Lean_Expr_appFnCleanup(x_20, lean_box(0));
x_26 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Expr_isApp(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Expr_appFnCleanup(x_25, lean_box(0));
x_32 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_24);
lean_dec(x_19);
x_34 = l_Lean_Expr_isApp(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appArg(x_31, lean_box(0));
x_38 = l_Lean_Expr_appFnCleanup(x_31, lean_box(0));
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Expr_appFnCleanup(x_38, lean_box(0));
x_43 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9;
x_44 = l_Lean_Expr_isConstOf(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11;
x_46 = l_Lean_Expr_isConstOf(x_42, x_45);
lean_dec(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
x_47 = lean_box(0);
x_48 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = lean_apply_10(x_14, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_42);
lean_dec(x_1);
x_50 = lean_apply_10(x_14, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_31);
x_51 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1(x_1, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_25);
x_52 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3(x_1, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_introNewHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_List_reverse___rarg(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_Grind_intros(x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_appendTR___rarg(x_17, x_2);
x_1 = x_15;
x_2 = x_19;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
x_15 = lean_ctor_get(x_1, 7);
x_16 = lean_ctor_get(x_1, 8);
x_17 = lean_ctor_get(x_1, 9);
x_18 = lean_ctor_get(x_1, 10);
x_19 = lean_ctor_get(x_1, 11);
x_20 = lean_ctor_get(x_1, 12);
x_21 = lean_ctor_get(x_1, 13);
x_22 = lean_ctor_get(x_1, 14);
x_23 = lean_ctor_get(x_1, 15);
x_24 = lean_ctor_get(x_1, 16);
x_25 = lean_ctor_get(x_1, 17);
x_26 = lean_ctor_get(x_1, 18);
x_27 = lean_ctor_get(x_1, 19);
x_28 = lean_ctor_get(x_1, 20);
x_29 = lean_ctor_get(x_1, 21);
x_30 = lean_ctor_get(x_1, 22);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_31, 3, x_10);
lean_ctor_set(x_31, 4, x_11);
lean_ctor_set(x_31, 5, x_12);
lean_ctor_set(x_31, 6, x_13);
lean_ctor_set(x_31, 7, x_15);
lean_ctor_set(x_31, 8, x_16);
lean_ctor_set(x_31, 9, x_17);
lean_ctor_set(x_31, 10, x_18);
lean_ctor_set(x_31, 11, x_19);
lean_ctor_set(x_31, 12, x_20);
lean_ctor_set(x_31, 13, x_21);
lean_ctor_set(x_31, 14, x_22);
lean_ctor_set(x_31, 15, x_23);
lean_ctor_set(x_31, 16, x_24);
lean_ctor_set(x_31, 17, x_25);
lean_ctor_set(x_31, 18, x_26);
lean_ctor_set(x_31, 19, x_27);
lean_ctor_set(x_31, 20, x_28);
lean_ctor_set(x_31, 21, x_29);
lean_ctor_set(x_31, 22, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*23, x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_31);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_ctor_get(x_1, 4);
x_39 = lean_ctor_get(x_1, 5);
x_40 = lean_ctor_get(x_1, 6);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
x_42 = lean_ctor_get(x_1, 7);
x_43 = lean_ctor_get(x_1, 8);
x_44 = lean_ctor_get(x_1, 9);
x_45 = lean_ctor_get(x_1, 10);
x_46 = lean_ctor_get(x_1, 11);
x_47 = lean_ctor_get(x_1, 12);
x_48 = lean_ctor_get(x_1, 13);
x_49 = lean_ctor_get(x_1, 14);
x_50 = lean_ctor_get(x_1, 15);
x_51 = lean_ctor_get(x_1, 16);
x_52 = lean_ctor_get(x_1, 17);
x_53 = lean_ctor_get(x_1, 18);
x_54 = lean_ctor_get(x_1, 19);
x_55 = lean_ctor_get(x_1, 20);
x_56 = lean_ctor_get(x_1, 21);
x_57 = lean_ctor_get(x_1, 22);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_58 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set(x_58, 4, x_38);
lean_ctor_set(x_58, 5, x_39);
lean_ctor_set(x_58, 6, x_40);
lean_ctor_set(x_58, 7, x_42);
lean_ctor_set(x_58, 8, x_43);
lean_ctor_set(x_58, 9, x_44);
lean_ctor_set(x_58, 10, x_45);
lean_ctor_set(x_58, 11, x_46);
lean_ctor_set(x_58, 12, x_47);
lean_ctor_set(x_58, 13, x_48);
lean_ctor_set(x_58, 14, x_49);
lean_ctor_set(x_58, 15, x_50);
lean_ctor_set(x_58, 16, x_51);
lean_ctor_set(x_58, 17, x_52);
lean_ctor_set(x_58, 18, x_53);
lean_ctor_set(x_58, 19, x_54);
lean_ctor_set(x_58, 20, x_55);
lean_ctor_set(x_58, 21, x_56);
lean_ctor_set(x_58, 22, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*23, x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
x_2 = x_34;
x_3 = x_59;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1(x_13, x_2, x_15);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_introNewHyp(x_16, x_15, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_Grind_cases(x_23, x_18, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_splitNext___lambda__2(x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_st_ref_get(x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_41 = l_Lean_Meta_Grind_casesMatch(x_40, x_1, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_Grind_splitNext___lambda__2(x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_4);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", generation: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_splitNext___lambda__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_21; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_10 = x_24;
x_11 = x_23;
goto block_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
lean_dec(x_22);
lean_inc(x_26);
x_29 = l_Lean_Meta_Grind_getGeneration(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_73; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_lt(x_32, x_27);
lean_dec(x_27);
x_34 = l_Lean_Meta_Grind_splitNext___lambda__4___closed__1;
x_73 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
if (x_33 == 0)
{
if (x_28 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
lean_inc(x_30);
x_35 = x_30;
x_36 = x_76;
x_37 = x_75;
goto block_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_nat_add(x_30, x_32);
x_80 = lean_unbox(x_77);
lean_dec(x_77);
x_35 = x_79;
x_36 = x_80;
x_37 = x_78;
goto block_72;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_dec(x_73);
x_83 = lean_nat_add(x_30, x_32);
x_84 = lean_unbox(x_81);
lean_dec(x_81);
x_35 = x_83;
x_36 = x_84;
x_37 = x_82;
goto block_72;
}
block_72:
{
if (x_36 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_38 = lean_box(0);
lean_inc(x_1);
x_39 = l_Lean_Meta_Grind_splitNext___lambda__3(x_26, x_35, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_10 = x_40;
x_11 = x_41;
goto block_20;
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Grind_updateLastTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_26);
x_48 = l_Lean_MessageData_ofExpr(x_26);
x_49 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Meta_Grind_splitNext___lambda__4___closed__3;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_MessageData_ofFormat(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
x_58 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_34, x_57, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_1);
x_61 = l_Lean_Meta_Grind_splitNext___lambda__3(x_26, x_35, x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_10 = x_62;
x_11 = x_63;
goto block_20;
}
else
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
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
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
return x_46;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_46, 0);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_46);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_29);
if (x_85 == 0)
{
return x_29;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_29, 0);
x_87 = lean_ctor_get(x_29, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_29);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_21);
if (x_89 == 0)
{
return x_21;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_21, 0);
x_91 = lean_ctor_get(x_21, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_21);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
block_20:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_1, x_11);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lambda__4), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_splitNext___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at_Lean_Meta_Grind_splitNext___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_splitNext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_splitNext___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedCaseSplitStatus = _init_l_Lean_Meta_Grind_instInhabitedCaseSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCaseSplitStatus);
l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1 = _init_l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqCaseSplitStatus___closed__1);
l_Lean_Meta_Grind_instBEqCaseSplitStatus = _init_l_Lean_Meta_Grind_instBEqCaseSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqCaseSplitStatus);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__2);
l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__3);
l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__4);
l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___spec__1___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__2___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__6);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__7);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__8);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___lambda__5___closed__9);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__6);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__7);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__8);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__9);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__10);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkCaseSplitStatus___closed__11);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__6);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__7);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__1___closed__8);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1);
l_Lean_Meta_Grind_splitNext___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lambda__4___closed__1);
l_Lean_Meta_Grind_splitNext___lambda__4___closed__2 = _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lambda__4___closed__2);
l_Lean_Meta_Grind_splitNext___lambda__4___closed__3 = _init_l_Lean_Meta_Grind_splitNext___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lambda__4___closed__3);
l_Lean_Meta_Grind_splitNext___closed__1 = _init_l_Lean_Meta_Grind_splitNext___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
